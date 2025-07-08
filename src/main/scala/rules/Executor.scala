// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silver.cfg.silver.SilverCfg
import viper.silver.cfg.silver.SilverCfg.{SilverBlock, SilverEdge}
import viper.silver.verifier.{CounterexampleTransformer, PartialVerificationError}
import viper.silver.verifier.errors._
import viper.silver.verifier.reasons._
import viper.silver.{ast, cfg}
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.RecordedPathConditions
import viper.silicon.interfaces._
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.records.data._
import viper.silicon.resources.FieldID
import viper.silicon.state._
import viper.silicon.state.terms._
import viper.silicon.state.terms.perms.IsPositive
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.supporters.Translator
import viper.silicon.utils.{freshSnap, zip3}
import viper.silicon.utils.consistency.createUnexpectedNodeError
import viper.silicon.verifier.Verifier

trait ExecutionRules extends SymbolicExecutionRules {
  def exec(s: State,
           cfg: SilverCfg,
           v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult

  def exec(s: State, stmt: ast.Stmt, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult

  def execs(s: State, stmts: Seq[ast.Stmt], v: Verifier)
           (Q: (State, Verifier) => VerificationResult)
           : VerificationResult
}

object executor extends ExecutionRules with Immutable {

  import consumer._
  import evaluator._
  import producer._
  import wellFormedness._

  private def follow(s: State, originatingBlock: SilverBlock, edge: SilverEdge, v: Verifier)
                    (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    def handleOutEdge(s: State, originatingBlock: SilverBlock, edge: SilverEdge, v: Verifier) = {
      // state after loop is created here?
      edge.kind match {
        // in edges go into loops
        // out edges lead out of loops (and maybe to another loop)
        // normal edges are between statements (which are not loops)
        case cfg.Kind.Out => {
          val (fr1, h1) = stateConsolidator.merge(s.functionRecorder, s.h, s.invariantContexts.head._3, v)
          val (fr2, oh) = stateConsolidator.merge(fr1, s.optimisticHeap, s.invariantContexts.head._4, v)

          val potentialCheckPosition: Option[CheckPosition.Loop] = {
            val loopInvariant = originatingBlock match {
              case cfg.LoopHeadBlock(invs, _) => Some(invs)
              case _ => None
            }

            loopInvariant match {
              case Some(invs) => Some(CheckPosition.Loop(invs, LoopPosition.After))
              case None => None
            }
          }

          val s1 = s.copy(functionRecorder = fr2,
            isImprecise = s.invariantContexts.head._2, h = h1, optimisticHeap = oh,
            invariantContexts = s.invariantContexts.tail,
            loopPosition = potentialCheckPosition)

          s1
        }
        case _ =>
          /* No need to do anything special. See also the handling of loop heads in exec below. */
          s
      }
      // set the after loop state here
    }

    // TODO: ASK JENNA where the loop location needs to be available here
    // we continue after the loop here
    // conditional edge: follow came from a loop
    edge match {
      case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] =>
        val condEdgeRecord = new ConditionalEdgeRecord(ce.condition, s, v.decider.pcs)
        val sepIdentifier = SymbExLogger.currentLog().openScope(condEdgeRecord)
        val s1 = handleOutEdge(s, originatingBlock, edge, v)
        // condition being negated here
        eval(s1, ce.condition, IfFailed(ce.condition), v)((s2, tCond, v1) => {
        /* Eval here likely results in the creation of two run-time checks for the same field when framing loop conditions:
         * one in this eval + one in the eval in the loop block IN-edge case, both located before the loop.
         * It will also create one for framing !e after loop, which is correct and should be kept. - JW
         */
          /* Using branch(...) here ensures that the edge condition is recorded
           * as a branch condition on the pathcondition stack.
           */

          val s2point5 = s2.copy(loopPosition = None)
          val positionalCondition = ce.condition match {
            case ast.Not(e) => e
            case _ => ce.condition
          }

          // The loop location should be set for this branch, maybe
          brancher.branch(s2point5, tCond, positionalCondition, s1.loopPosition, v1)(
            (s3, v3) =>
              exec(s3, ce.target, ce.kind, v3)((s4, v4) => {
                SymbExLogger.currentLog().closeScope(sepIdentifier)
                Q(s4, v4)
              }),
            (_, _) => {
              SymbExLogger.currentLog().closeScope(sepIdentifier)
              Unreachable()
            })
        })

      // TODO: Should we be tracking loop positions here, too?
      case ue: cfg.UnconditionalEdge[ast.Stmt, ast.Exp] =>

        val s1 = handleOutEdge(s, originatingBlock, edge, v)
        val s1point5 = s1.copy(loopPosition = None)

        exec(s1point5, ue.target, ue.kind, v)(Q)
    }
  }

  private def follows(s: State,
                      originatingBlock: SilverBlock,
                      edges: Seq[SilverEdge],
                      pvef: ast.Exp => PartialVerificationError,
                      v: Verifier)
                     (Q: (State, Verifier) => VerificationResult)
  : VerificationResult = {

    if (edges.isEmpty) {
      Q(s, v)
    } else {
      val isImprecise = originatingBlock match {
        case cfg.LoopHeadBlock(_, _) => s.invariantContexts.head._1
        case _ => s.isImprecise
      }
      if (isImprecise) {
        val uidBranchPoint = if (edges.length > 1) { SymbExLogger.currentLog().insertBranchPoint(edges.length) } else { 0 }
        val rsTuple =
        edges.zipWithIndex.foldLeft((Unreachable(): VerificationResult, edges.head: SilverEdge)) { (rs, eTuple) =>
          val (edge, edgeIndex) = eTuple
          if (edges.length > 1) {
            if (edgeIndex != 0) {
              SymbExLogger.currentLog().switchToNextBranch(uidBranchPoint)
            }
            SymbExLogger.currentLog().markReachable(uidBranchPoint)
          }
          val rsEdge = follow(s, originatingBlock, edge, v)(Q)
          rs match {
            case (Success(), prevEdge) => {
              rsEdge match {
                case Success() | Unreachable() => (Success(), edge)
                case Failure(m) => {
                  edge match {
                    case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] => {
                      edge.kind match {
                        case cfg.Kind.Out => (Failure(m), edge)
                        case _ => {
                          /* run-time check */
                          val position: ast.Exp =
                            prevEdge.asInstanceOf[cfg.ConditionalEdge[ast.Stmt, ast.Exp]].condition match {
                              case ast.Not(e: ast.Exp) => e
                              case e: ast.Exp => e
                            }

                          if (s.generateChecks) {
                            runtimeChecks.addChecks(CheckPosition.GenericNode(position),
                              prevEdge.asInstanceOf[cfg.ConditionalEdge[ast.Stmt, ast.Exp]].condition,
                              viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                                v.decider.pcs.branchConditionsAstNodes,
                                v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                              position,
                              false)
                          }

                          (Success(), edge)
                        }
                      }
                    }
                    case _ => (Failure(m), edge)
                  }
                }
              }
            }
            case (Unreachable(), prevEdge) => (rsEdge, edge)
            case (Failure(m), prevEdge) => {
              rsEdge match {
                case Success() => {
                  edge match {
                    case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] => {
                      prevEdge.kind match {
                        case cfg.Kind.Out => (Failure(m), edge)
                        case _ => {
                          /* run-time check */
                          val position: ast.Exp =
                            edge.asInstanceOf[cfg.ConditionalEdge[ast.Stmt, ast.Exp]].condition match {
                              case ast.Not(e: ast.Exp) => e
                              case e: ast.Exp => e
                            }
                          if (s.generateChecks) {
                            runtimeChecks.addChecks(CheckPosition.GenericNode(position),
                              edge.asInstanceOf[cfg.ConditionalEdge[ast.Stmt, ast.Exp]].condition,
                              viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                                v.decider.pcs.branchConditionsAstNodes,
                                v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                              position,
                              false)
                          }

                          (Success(), edge)
                        }
                      }
                    }
                    case _ => (Failure(m), edge)
                  }
                }
                case Unreachable() => (rs._1, edge)
                case Failure(_) => (rs._1 && rsEdge, edge)
              }
            }
          }
        }
        if (edges.length > 1) {
          SymbExLogger.currentLog().endBranchPoint(uidBranchPoint)
        }
        rsTuple._1
      } else {
        // if not imprecise
        if (edges.length == 1) {
          follow(s, originatingBlock, edges.head, v)(Q)
        } else {
          val uidBranchPoint = SymbExLogger.currentLog().insertBranchPoint(edges.length)
          val res = edges.zipWithIndex.foldLeft(Success(): VerificationResult) {
            case (fatalResult: FatalResult, _) => fatalResult
            case (_, (edge, edgeIndex)) =>
              if (edgeIndex != 0) {
                SymbExLogger.currentLog().switchToNextBranch(uidBranchPoint)
              }
              SymbExLogger.currentLog().markReachable(uidBranchPoint)
              follow(s, originatingBlock, edge, v)(Q)
          }
          SymbExLogger.currentLog().endBranchPoint(uidBranchPoint)
          res
        }
      }
    }
  }

  def exec(s: State, graph: SilverCfg, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    exec(s, graph.entry, cfg.Kind.Normal, v)(Q)
  }

  def exec(s: State, block: SilverBlock, incomingEdgeKind: cfg.Kind.Value, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {

    block match {
      case cfg.StatementBlock(stmt) =>
        execs(s, stmt, v)((s1, v1) =>
          follows(s1, block, magicWandSupporter.getOutEdges(s1, block), IfFailed, v1)(Q))

      case   _: cfg.PreconditionBlock[ast.Stmt, ast.Exp]
           | _: cfg.PostconditionBlock[ast.Stmt, ast.Exp] =>

        /* It is expected that the CFG of a method *body* is executed, not that of
         * the whole method (which includes pre-/postcondition blocks).
         * See also the MethodSupporter.
         */
        sys.error(s"Unexpected block: $block")

      case block @ cfg.LoopHeadBlock(invs, stmts) =>
        // we use the first invariant in invs because invs is a Seq[ast.Exp]
        // and a Seq may be mutable in CFGs produced by gvc0
        incomingEdgeKind match {
          case cfg.Kind.In =>
            /* We've reached a loop head block via an in-edge. Steps to perform:
             *   - Check loop invariant for self-framingness
             *   - Check that the loop guard is framed by the invariant
             *   - Exhale invariant of the target block
             *   - Push leftover state onto invariant context stack
             *   - Create state in which to execute the loop body by producing the
             *     invariant into an empty heap
             *   - Execute the statements in the loop head block
             *   - Follow the outgoing edges
             */
            val sepIdentifier = SymbExLogger.currentLog().openScope(
              new LoopInRecord(invs.head, s, v.decider.pcs))

            /* Havoc local variables that are assigned to in the loop body */
            val wvs = s.methodCfg.writtenVars(block)
              /* TODO: BUG: Variables declared by LetWand show up in this list, but shouldn't! */

            val gBody = Store(wvs.foldLeft(s.g.values)((map, x) => {
              /* 2025-01-29 Long:
               * havoc variables will get a new suffix and will not show up
               * in freshPositions, so we need to add them to freshPositions
               */
              val freshVar = v.decider.fresh(x)
              val existingTerm = map.get(x)
              /* if the variable cannot be found in freshPositions, it means
               * that it has not been assigned to yet
               */
              existingTerm match {
                case Some(term) =>
                  if (SymbExLogger.enabled && SymbExLogger.freshPositions.contains(term)) {
                    SymbExLogger.freshPositions += freshVar -> SymbExLogger.freshPositions(term)
                  }
                case None =>
              }
              map.updated(x, freshVar)
            } ))
            val sBody = s.copy(isImprecise = false,
                               g = gBody,
                               h = Heap(),
                               optimisticHeap = Heap())

            val edges = s.methodCfg.outEdges(block)
            val (outEdges, otherEdges) = edges partition(_.kind == cfg.Kind.Out)
            val sortedEdges = otherEdges ++ outEdges
            // extracts all the conditions from the edges (from the statements
            // that make them up?)
            //
            // keeps the unique ones
            val edgeConditions = sortedEdges.collect{case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] => ce.condition}
                                            .distinct

            type PhaseData = (State, RecordedPathConditions, InsertionOrderedSet[FunctionDecl])
            var phase1data: Vector[PhaseData] = Vector.empty

            (executionFlowController.locally(sBody, v)((s0, v0) => {
                v0.decider.prover.comment("Loop head block: Check well-definedness of invariant")
                val mark = v0.decider.setPathConditionMark()

                wellformed(
                  s0.copy(loopPosition = Some(CheckPosition.Loop(invs, LoopPosition.Beginning))),
                  freshSnap,
                  invs,
                  ContractNotWellformed(viper.silicon.utils.ast.BigAnd(invs)),
                  v0)((s1, v1) => {   //pve is a placeholder
                  SymbExLogger.currentLog().closeScope(sepIdentifier)
                  val s1point5 = s1.copy(loopPosition = None)

                  // unset for at beginning of loop body
                  // produces into phase1data
                  phase1data = phase1data :+ (s1point5,
                                              v1.decider.pcs.after(mark),
                                              InsertionOrderedSet.empty[FunctionDecl] /*v2.decider.freshFunctions*/ /* [BRANCH-PARALLELISATION] */)
                  v1.decider.prover.comment("Loop head block: Check well-definedness of edge conditions")
                  edgeConditions.foldLeft(Success(): VerificationResult) {
                    case (fatalResult: FatalResult, _) => fatalResult
                    case (intermediateResult, eCond) =>
                      intermediateResult && executionFlowController.locally(s1point5, v1)((s2, v2) => {
                        eval(s2, eCond, WhileFailed(eCond), v2)((_, _, _) =>
                          Success())})}})})

            && executionFlowController.locally(s, v)((s0, v0) => {
                v0.decider.prover.comment("Loop head block: Establish invariant")
                consumes(s0.copy(loopPosition = Some(CheckPosition.Loop(invs, LoopPosition.Before))),
                  invs, LoopInvariantNotEstablished, v0)((sLeftover0, _, v1) => {
                  
                  var sLeftover1 = sLeftover0
                  if (isEquiImp(invs))
                    sLeftover1 = sLeftover0.copy(h = Heap(),
                      optimisticHeap = Heap(),
                      isImprecise = true)

                  val sLeftover = sLeftover1.copy(loopPosition = None)
                  
                  // unset enum for before loop in symbolic state here?
                  v1.decider.prover.comment("Loop head block: Execute statements of loop head block (in invariant state)")

                  phase1data.foldLeft(Success(): VerificationResult) {
                    case (fatalResult: FatalResult, _) => fatalResult
                    case (intermediateResult, (s1, pcs, ff1)) => /* [BRANCH-PARALLELISATION] ff1 */
                      val s2 = s1.copy(invariantContexts = (s0.isImprecise, sLeftover.isImprecise, sLeftover.h, sLeftover.optimisticHeap) +: s1.invariantContexts)
                      intermediateResult && executionFlowController.locally(s2, v1)((s3, v2) => {
  //                    v2.decider.declareAndRecordAsFreshFunctions(ff1 -- v2.decider.freshFunctions) /* [BRANCH-PARALLELISATION] */
                        v2.decider.assume(pcs.assumptions)
                        v2.decider.prover.saturate(Verifier.config.z3SaturationTimeouts.afterContract)
                        if (v2.decider.checkSmoke())
                          Success()
                        else {
                          execs(s3, stmts, v2)((s4, v3) => {
                            v3.decider.prover.comment("Loop head block: Follow loop-internal edges")
                            follows(s4, block, sortedEdges, WhileFailed, v3)(Q)})}})}})}))

          case _ =>
            /* We've reached a loop head block via an edge other than an in-edge: a normal edge or
             * and out-edge. We consider this edge to be a back-edge and we break the cycle by
             * attempting to re-establish the invariant.
             */
            v.decider.prover.comment("Loop head block: Re-establish invariant")
            // this is the consume at the end of the loop body
            
            val s0 = s.copy(loopPosition = Some(CheckPosition.Loop(invs, LoopPosition.End)))

            val edges = s0.methodCfg.outEdges(block)
            val (outEdges, otherEdges) = edges partition(_.kind == cfg.Kind.Out)
            val sortedEdges = otherEdges ++ outEdges
            // extracts all the conditions from the edges (from the statements
            // that make them up?)
            //
            // keeps the unique ones
            val edgeConditions =
              sortedEdges
                .collect{case ce: cfg.ConditionalEdge[ast.Stmt, ast.Exp] => ce.condition}
                .distinct
            
            // call eval on the loop condition to get checks for framing it if needed
            eval(s0, edgeConditions.head, IfFailed(edgeConditions.head), v)((_, _, _) => 
              Success())
            val sepIdentifier = SymbExLogger.currentLog().openScope(
              new LoopOutRecord(invs.head, s0, v.decider.pcs))
            // consume the loop invariant
            consumes(s0, invs, e => LoopInvariantNotPreserved(e), v)((s1, _, v1) => {
              SymbExLogger.currentLog().closeScope(sepIdentifier)
              val sepIdentifier2 = SymbExLogger.currentLog().openScope(
                new EndRecord(s1, v1.decider.pcs))
              SymbExLogger.currentLog().closeScope(sepIdentifier2)
              Success()})
        }

      case cfg.ConstrainingBlock(vars: Seq[ast.AbstractLocalVar @unchecked], body: SilverCfg) =>
        val arps = vars map (s.g.apply(_).asInstanceOf[Var])
        exec(s.setConstrainable(arps, true), body, v)((s1, v1) =>
          follows(s1.setConstrainable(arps, false), block, magicWandSupporter.getOutEdges(s1, block), Internal(_), v1)(Q))
    }
  }

  def execs(s: State, stmts: Seq[ast.Stmt], v: Verifier)
           (Q: (State, Verifier) => VerificationResult)
           : VerificationResult =

    if(stmts.nonEmpty)
      exec(s, stmts.head, v)((s1, v1) =>
        execs(s1, stmts.tail, v1)(Q))
    else
      Q(s, v)

  def exec(s: State, stmt: ast.Stmt, v: Verifier)
          (Q: (State, Verifier) => VerificationResult)
          : VerificationResult = {
    val sepIdentifier = SymbExLogger.currentLog().openScope(new ExecuteRecord(stmt, s, v.decider.pcs))
    exec2(s, stmt, v)((s1, v1) => {
      SymbExLogger.currentLog().closeScope(sepIdentifier)
      Q(s1, v1)})
  }

  def exec2(state: State, stmt: ast.Stmt, v: Verifier)
           (continuation: (State, Verifier) => VerificationResult)
           : VerificationResult = {

    val s = state.copy(h=magicWandSupporter.getExecutionHeap(state))
    val Q: (State, Verifier) => VerificationResult = (s, v) => {
      continuation(magicWandSupporter.moveToReserveHeap(s, v), v)}

    /* For debugging-purposes only */
    stmt match {
      case _: ast.Seqn =>
      case _ =>
        v.logger.debug(s"\nEXECUTE ${viper.silicon.utils.ast.sourceLineColumn(stmt)}: $stmt")
        v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
        if (s.reserveHeaps.nonEmpty)
          v.logger.debug("hR = " + s.reserveHeaps.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
        v.decider.prover.comment("[exec]")
        v.decider.prover.comment(stmt.toString())
    }

    val executed = stmt match {
      case ast.Seqn(stmts, _) =>
        execs(s, stmts, v)(Q)

      /*
      case ast.Label(name, _) =>
        val s1 = s.copy(oldHeaps = s.oldHeaps + (name -> magicWandSupporter.getEvalHeap(s)))
        Q(s1, v)
      */

      case ast.LocalVarDeclStmt(decl) =>
        val x = decl.localVar
        val t = v.decider.fresh(x.name, v.symbolConverter.toSort(x.typ))
        Q(s.copy(g = s.g + (x -> t)), v)

      case ass @ ast.LocalVarAssign(x, rhs) =>
        eval(s, rhs, AssignmentFailed(ass), v)((s1, tRhs, v1) => {
          val t = ssaifyRhs(tRhs, x.name, x.typ, v, ass.pos)
          Q(s1.copy(g = s1.g + (x, t)), v1)
        })

      /* TODO: Encode assignments e1.f := e2 as
       *         exhale acc(e1.f)
       *         inhale acc(e1.f) && e1.f == e2
       *       and benchmark possible performance effects.
       */

      /* Assignment for a field that contains quantified chunks */
      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs)
        if s.qpFields.contains(field) => sys.error(s"Quantified permissions not supported for the field in (${stmt.getClass.getName}): $stmt")
      /*
      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs)
              if s.qpFields.contains(field) =>

        assert(!s.exhaleExt)
        val pve = AssignmentFailed(ass)
        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, rhs, pve, v1)((s2, tRhs, v2) => {
            val (relevantChunks, otherChunks) =
              quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s2.h, BasicChunkIdentifier(field.name))
            val hints = quantifiedChunkSupporter.extractHints(None, Seq(tRcvr))
            val chunkOrderHeuristics = quantifiedChunkSupporter.hintBasedChunkOrderHeuristic(hints)
            val (smDef1, smCache1) =
              quantifiedChunkSupporter.summarisingSnapshotMap(
                s2, field, Seq(`?r`), relevantChunks, v1)
            v2.decider.assume(FieldTrigger(field.name, smDef1.sm, tRcvr))
            v2.decider.clearModel()
            val result = quantifiedChunkSupporter.removePermissions(
              s2.copy(smCache = smCache1),
              relevantChunks,
              Seq(`?r`),
              `?r` === tRcvr,
              field,
              FullPerm(),
              chunkOrderHeuristics,
              v2
            )
            result match {
              case (Complete(), s3, remainingChunks) =>
                val h3 = Heap(remainingChunks ++ otherChunks)
                val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s3, field, Seq(tRcvr), tRhs, v2)
                v1.decider.prover.comment("Definitional axioms for singleton-FVF's value")
                v1.decider.assume(smValueDef)
                val ch = quantifiedChunkSupporter.createSingletonQuantifiedChunk(Seq(`?r`), field, Seq(tRcvr), FullPerm(), sm)
                v1.decider.assume(FieldTrigger(field.name, sm, tRcvr))
                Q(s3.copy(h = h3 + ch), v2)
              case (Incomplete(_), s3, _) =>
                createFailure(pve dueTo InsufficientPermission(fa), v2, s3)}}))
*/

      case ass @ ast.FieldAssign(fa @ ast.FieldAccess(eRcvr, field), rhs) =>
       
        assert(!s.exhaleExt)
        val pve = AssignmentFailed(ass)

        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          eval(s1, rhs, pve, v1)((s2, tRhs, v2) => {
            val fap = ast.FieldAccessPredicate(fa, ast.FullPerm()(ass.pos))(ass.pos)

            consume(s2, fap, pve, v2)((s3, snap, v3) => {

              // TODO;EXTRA CHECK ISSUE(S): We assume the Ref is !== null here
              v3.decider.assume(tRcvr !== Null())
              val tSnap = ssaifyRhs(tRhs, field.name, field.typ, v3, ass.pos)
              val id = BasicChunkIdentifier(field.name)
              val newChunk = BasicChunk(FieldID, id, Seq(tRcvr), tSnap, FullPerm())

              chunkSupporter.produce(s3, s3.h, newChunk, v3)((s4, h4, v4) => {
              Q(s4.copy(h = h4), v4)})
            })
          })
        )

      case ast.NewStmt(x, fields) =>
        val tRcvr = v.decider.fresh(x)
        v.decider.assume(tRcvr !== Null())
        val newChunks = fields map (field => {
          val p = FullPerm()
          val snap = v.decider.fresh(field.name, v.symbolConverter.toSort(field.typ))
          if (s.qpFields.contains(field)) {
            val (sm, smValueDef) = quantifiedChunkSupporter.singletonSnapshotMap(s, field, Seq(tRcvr), snap, v)
            v.decider.prover.comment("Definitional axioms for singleton-FVF's value")
            v.decider.assume(smValueDef)
            quantifiedChunkSupporter.createSingletonQuantifiedChunk(Seq(`?r`), field, Seq(tRcvr), p, sm)
          } else {
            BasicChunk(FieldID, BasicChunkIdentifier(field.name), Seq(tRcvr), snap, p)
          }
        })
        val ts = viper.silicon.state.utils.computeReferenceDisjointnesses(s, tRcvr)
        val s1 = s.copy(g = s.g + (x, tRcvr), h = s.h + Heap(newChunks))
        v.decider.assume(ts)
        Q(s1, v)

      // commenting this out causes disjunction_fast to fail
      // also I think we have a problem with error messages
      
      case inhale @ ast.Inhale(a) => a match {
        case _: ast.FalseLit =>
          Success()
        case _ =>
          produce(s, freshSnap, a, InhaleFailed(inhale), v)((s1, v1) => {
            v1.decider.prover.saturate(Verifier.config.z3SaturationTimeouts.afterInhale)
            Q(s1, v1)})
      }

      case exhale @ ast.Exhale(a) =>
        val pve = ExhaleFailed(exhale)
        consume(s, a, pve, v)((s1, _, v1) =>
          Q(s1, v1))
      
      case assert @ ast.Assert(a) =>
        val pve = AssertFailed(assert)

        a match {
          /* "assert true" triggers a heap compression. */
          case _: ast.TrueLit =>
            val s1 = stateConsolidator.consolidate(s, v)
            Q(s1, v)

          /* "assert false" triggers a smoke check. If successful, we backtrack. */
          case _: ast.FalseLit =>
            executionFlowController.tryOrFail0(s.copy(h = magicWandSupporter.getEvalHeap(s)), v)((s1, v1, QS) => {
              if (v1.decider.checkSmoke())
                QS(s1.copy(h = s.h), v1)
              else
                createFailure(pve dueTo AssertionFalse(a), v1, s1)
            })((_, _) => Success())

          case _ =>
            if (Verifier.config.disableSubsumption()) {
              //This case resembles what's written in the PhD thesis
              consume(s, a, pve, v)((s1, snap1, v1) =>
                wellformed(s1.copy(isImprecise = true), freshSnap, Seq(a), pve, v1)((s2, v2) =>
                  Q(s, v2))
              )
            } else if (s.exhaleExt) {
              Predef.assert(s.h.values.isEmpty)
              Predef.assert(s.reserveHeaps.head.values.isEmpty)

              /* When exhaleExt is set magicWandSupporter.transfer is used to transfer permissions to
               * hUsed (reserveHeaps.head) instead of consuming them. hUsed is later discarded and replaced
               * by s.h. By copying hUsed to s.h the contained permissions remain available inside the wand.
               */
              consume(s, a, pve, v)((s1, snap1, v1) => {
                wellformed(s1.copy(isImprecise = true), freshSnap, Seq(a), pve, v1)((s2, v2) =>
                  Q(s2.copy(isImprecise = s.isImprecise, h = s2.reserveHeaps.head, optimisticHeap = s.optimisticHeap), v2))
              })
            } else {
              consume(s, a, pve, v)((s1, snap1, v1) => {
                wellformed(s1.copy(isImprecise = true), freshSnap, Seq(a), pve, v1)((s2, v2) => {
                  val s3 = s2.copy(isImprecise = s.isImprecise, h = s.h, optimisticHeap = s.optimisticHeap, reserveHeaps = s.reserveHeaps)
                  Q(s3, v2)
                })
              })
            }
        }

      // TODO;BRANCH POSITIONING: what is this?
      // A call havoc_all_R() results in Silicon efficiently havocking all instances of resource R.
      // See also Silicon issue #407.
      case call @ ast.MethodCall(methodName, _, _)
        if !Verifier.config.disableHavocHack407() && methodName.startsWith(hack407_method_name_prefix) => {

        sys.error("Do not use havoc_all_R(); it is not supported by Gradual Silicon! Aborting safely...")

        val resourceName = methodName.stripPrefix(hack407_method_name_prefix)
        val member = Verifier.program.collectFirst {
          case m: ast.Field if m.name == resourceName => m
          case m: ast.Predicate if m.name == resourceName => m
        }.getOrElse(sys.error(s"Found $methodName, but no matching field or predicate $resourceName"))
        val h1 = Heap(s.h.values.map {
          case bc: BasicChunk if bc.id.name == member.name =>
            bc.withSnap(freshSnap(bc.snap.sort, v))
          case qfc: QuantifiedFieldChunk if qfc.id.name == member.name =>
            qfc.withSnapshotMap(freshSnap(qfc.fvf.sort, v))
          case qpc: QuantifiedPredicateChunk if qpc.id.name == member.name =>
            qpc.withSnapshotMap(freshSnap(qpc.psf.sort, v))
          case other =>
            other
        })
        Q(s.copy(h = h1), v)

      }

      case call @ ast.MethodCall(methodName, eArgs, lhs) =>
        val meth = Verifier.program.findMethod(methodName)
        val fargs = meth.formalArgs.map(_.localVar)
        val formalsToActuals: Map[ast.LocalVar, ast.Exp] = fargs.zip(eArgs)(collection.breakOut)
        val reasonTransformer = (n: viper.silver.verifier.errors.ErrorNode) => n.replace(formalsToActuals)
        val pveCall = CallFailed(call).withReasonNodeTransformed(reasonTransformer)

        val mcLog = new MethodCallRecord(call, s, v.decider.pcs)
        val currentLog = SymbExLogger.currentLog()
        val sepIdentifier = currentLog.openScope(mcLog)
        val paramLog = new CommentRecord("Parameters", s, v.decider.pcs)
        val paramId = currentLog.openScope(paramLog)
        evals(s, eArgs, _ => pveCall, v)((s1, tArgs, v1) => {
          currentLog.closeScope(paramId)
          val exampleTrafo = CounterexampleTransformer({
            case ce: SiliconCounterexample => ce.withStore(s1.g)
            case ce => ce
          })
          val pvePre = ErrorWrapperWithExampleTransformer(PreconditionInCallFalse(call).withReasonNodeTransformed(reasonTransformer), exampleTrafo)
          val preCondLog = new CommentRecord("Precondition", s1, v1.decider.pcs)
          val preCondId = currentLog.openScope(preCondLog)
          // TODO: Fix this
          reconstructedPermissions.addMethodCallStatement(call,
            new Translator(s1, v1.decider.pcs).getAccessibilityPredicates,
            zip3(v1.decider.pcs.branchConditionsOrigins.map(entry => Null()),
              v1.decider.pcs.branchConditionsAstNodes,
              v1.decider.pcs.branchConditionsOrigins))

          // this is run unconditionally (or so it seems), so we can attach the
          // method call ast node here
          
          val s2 = s1.copy(g = Store(fargs.zip(tArgs)),
            oldStore = Some(s1.g),
            oldHeaps = s1.oldHeaps + (Verifier.PRE_HEAP_LABEL -> Heap()) + (Verifier.PRE_OPTHEAP_LABEL -> Heap()),
            recordVisited = true,
            methodCallAstNode = Some(call))

          consumes(s2, meth.pres, _ => pvePre, v1)((s3, _, v2) => {
            currentLog.closeScope(preCondId)
            val postCondLog = new CommentRecord("Postcondition", s3, v2.decider.pcs)
            val postCondId = currentLog.openScope(postCondLog)
            val outs = meth.formalReturns.map(_.localVar)
            val gOuts = Store(outs.map(x => (x, v2.decider.fresh(x))).toMap)
            val outOldStore = Store(lhs.zip(outs).map(p => (p._1, gOuts(p._2))).toMap)
            var s4p = s3

            if (isEquiImp(meth.pres))
              s4p = s3.copy(h = Heap(),
                optimisticHeap = Heap(),
                isImprecise = true)

            val s4 = s4p.copy(g = s3.g + gOuts,
              oldStore = Some(s1.g + outOldStore),
              oldHeaps = s3.oldHeaps + (Verifier.PRE_STATE_LABEL -> s1.h) + (Verifier.PRE_HEAP_LABEL -> s1.h) + (Verifier.PRE_OPTHEAP_LABEL -> s1.optimisticHeap))
            produces(s4, freshSnap, meth.posts, _ => pveCall, v2)((s5, v3) => {
              // we MUST unset both oldStore and the methodCallAstNode once we
              // are done with the method call
              val s6 = s5.copy(oldStore = None, methodCallAstNode = None)

              currentLog.closeScope(postCondId)

              v3.decider.prover.saturate(Verifier.config.z3SaturationTimeouts.afterContract)

              val gLhs = Store(lhs.zip(outs)
                .map(p => (p._1, s6.g(p._2))).toMap)

              val s7 = s6.copy(g = s1.g + gLhs,
                oldHeaps = s1.oldHeaps,
                recordVisited = s1.recordVisited)

              currentLog.closeScope(sepIdentifier)

              Q(s7, v3)
            })
          })
        })

      case fold @ ast.Fold(ast.PredicateAccessPredicate(ast.PredicateAccess(eArgs, predicateName), ePerm)) =>
        val predicate = Verifier.program.findPredicate(predicateName)
        val pve = FoldFailed(fold)
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1, ePerm, pve, v1)((s2, tPerm, v2) => {
            v2.decider.assertgv(s2.isImprecise, IsPositive(tPerm)) { //The IsPositive check is redundant
              case true =>
                val wildcards = s2.constrainableARPs -- s1.constrainableARPs
                predicateSupporter.fold(s2, predicate, Some(fold), tArgs, tPerm, wildcards, pve, v2)(Q)
              case false =>
                createFailure(pve dueTo NegativePermission(ePerm), v2, s2)
            } match {
              case (verificationResult, _) => verificationResult
            }
          }))

      case unfold @ ast.Unfold(ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm)) =>
        val predicate = Verifier.program.findPredicate(predicateName)
        val pve = UnfoldFailed(unfold)
        val sFrame = s.copy(gatherFrame = true)
        evals(sFrame, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          eval(s1.copy(gatherFrame = false), ePerm, pve, v1)((s2, tPerm, v2) => {

            val smCache1 = if (s2.qpPredicates.contains(predicate)) {
              val (relevantChunks, _) =
                quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](s2.h, BasicChunkIdentifier(predicateName))
              val (smDef1, smCache1) =
                quantifiedChunkSupporter.summarisingSnapshotMap(
                  s2, predicate, s2.predicateFormalVarMap(predicate), relevantChunks, v2)
              v2.decider.assume(PredicateTrigger(predicate.name, smDef1.sm, tArgs))
              smCache1
            } else {
              s2.smCache
            }

            v2.decider.assertgv(s2.isImprecise, IsPositive(tPerm)) { //The IsPositive check is redundant
              case true =>
                val wildcards = s2.constrainableARPs -- s1.constrainableARPs
                predicateSupporter.unfold(s2.copy(smCache = smCache1), predicate, Some(unfold), tArgs, tPerm, wildcards, pve, v2, pa)(Q)
              case false =>
                createFailure(pve dueTo NegativePermission(ePerm), v2, s2)
            } match {
              case (verificationResult, _) => verificationResult
            }
          }))

      /*
      case pckg @ ast.Package(wand, proofScript) =>
        val pve = PackageFailed(pckg)
          magicWandSupporter.packageWand(s, wand, proofScript, pve, v)((s1, chWand, v1) => {

            val hOps = s1.reserveHeaps.head + chWand
            assert(s.exhaleExt || s1.reserveHeaps.length == 1)
            val s2 =
              if (s.exhaleExt) {
                s1.copy(h = Heap(),
                        exhaleExt = true,
                         * It is assumed, that s.reserveHeaps.head (hUsed) is not used or changed
                         * by the packageWand method. hUsed is normally used during transferring
                         * consume to store permissions that have already been consumed. The
                         * permissions on this heap should be discarded after a statement finishes
                         * execution. hUsed should therefore be empty unless the package statement
                         * was triggered by heuristics during a consume operation.
                         *
                        reserveHeaps = s.reserveHeaps.head +: hOps +: s1.reserveHeaps.tail)
              } else {
                * c1.reserveHeap is expected to be [σ.h'], i.e. the remainder of σ.h *
                s1.copy(h = hOps,
                        exhaleExt = false,
                        reserveHeaps = Nil)
              }
            assert(s2.reserveHeaps.length == s.reserveHeaps.length)

            val smCache3 = chWand match {
              case ch: QuantifiedMagicWandChunk =>
                val (relevantChunks, _) =
                  quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](s2.h, ch.id)
                val bodyVars = wand.subexpressionsToEvaluate(Verifier.program)
                val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v1.symbolConverter.toSort(bodyVars(i).typ)))
                val (smDef, smCache) =
                  quantifiedChunkSupporter.summarisingSnapshotMap(
                    s2, wand, formalVars, relevantChunks, v1)
                v1.decider.assume(PredicateTrigger(ch.id.toString, smDef.sm, ch.singletonArgs.get))
                smCache
              case _ => s2.smCache
            }

            continuation(s2.copy(smCache = smCache3), v1)
          })

      case apply @ ast.Apply(e) =>
        val pve = ApplyFailed(apply)
        magicWandSupporter.applyWand(s, e, pve, v)(Q)
*/
      /* These cases should not occur when working with the CFG-representation of the program. */
      case _: ast.Goto
           | _: ast.If
           | _: ast.Label
           | _: ast.Seqn
           | _: ast.While => sys.error(s"Unexpected statement (${stmt.getClass.getName}): $stmt")

      /* These cases were commented out, because they are not supported by Silicon-gv. */
      case _: ast.Inhale
           | _: ast.Exhale
           | _: ast.Package
           | _: ast.Apply => createFailure(createUnexpectedNodeError(stmt,""), v, s)
    }

    executed
  }

   private def ssaifyRhs(rhs: Term, name: String, typ: ast.Type, v: Verifier, pos: ast.Position): Term = {
     rhs match {
       /* 2025-01-29 Long:
        * The following line used to be
        * case _: Var | _: Literal =>
        */
       case _: Literal =>
         rhs

       case _  =>
         /* 2018-06-05 Malte:
          *   This case was previously guarded by the condition
          *     rhs.existsDefined {
          *       case t if v.triggerGenerator.isForbiddenInTrigger(t) => true
          *     }
          *   and followed by a catch-all case in which rhs was returned.
          *   However, reducing the number of fresh symbols does not appear to improve
          *   performance; instead, it can cause an exponential blow-up in term size, as
          *   reported by Silicon issue #328.
          */
         val t = v.decider.fresh(name, v.symbolConverter.toSort(typ))
         v.decider.assume(t === rhs)
         /* 2025-01-29 Long:
          * record position where the Var was freshened in freshPositions
          * freshPositions should not contain this Var yet
          */
         if (SymbExLogger.enabled) {
           SymbExLogger.freshPositions += t -> pos
         }

         t
     }
   }

  private val hack407_method_name_prefix = "___silicon_hack407_havoc_all_"

  def hack407_havoc_all_resources_method_name(id: String): String = s"$hack407_method_name_prefix$id"

  def hack407_havoc_all_resources_method_call(id: String): ast.MethodCall = {
    ast.MethodCall(
      methodName = hack407_havoc_all_resources_method_name(id),
      args = Vector.empty,
      targets = Vector.empty
    )(ast.NoPosition, ast.NoInfo, ast.NoTrafos)
  }
}
