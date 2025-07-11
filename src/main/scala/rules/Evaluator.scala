// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.rules

import viper.silver.ast
import viper.silver.ast.utils.conjunctExps
import viper.silver.ast.{Info, PredicateAccess}
import viper.silver.verifier.{CounterexampleTransformer, PartialVerificationError}
import viper.silver.verifier.errors.{ErrorWrapperWithExampleTransformer, PreconditionInAppFalse}
import viper.silver.verifier.reasons._
import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.interfaces._
import viper.silicon.resources.PredicateID
import viper.silicon.state.{terms, _}
import viper.silicon.state.terms._
import viper.silicon.state.terms.implicits._
import viper.silicon.state.terms.perms.{IsNonNegative, IsPositive}
import viper.silicon.state.terms.predef.`?r`
import viper.silicon.supporters.Translator
import viper.silicon.utils.consistency.createUnexpectedNodeError
import viper.silicon.utils.toSf
import viper.silicon.utils.ast.flattenOperator
import viper.silicon.verifier.Verifier
import viper.silicon.{Map, TriggerSets}
import viper.silicon.interfaces.state.{ChunkIdentifer, NonQuantifiedChunk}
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.records.data.{EvaluateRecord, EvaluatePCRecord}

/* TODO: With the current design w.r.t. parallelism, eval should never "move" an execution
 *       to a different verifier. Hence, consider not passing the verifier to continuations
 *       of eval.
 */

trait EvaluationRules extends SymbolicExecutionRules {
  def evals(s: State, es: Seq[ast.Exp], pvef: ast.Exp => PartialVerificationError, v: Verifier)
           (Q: (State, List[Term], Verifier) => VerificationResult)
           : VerificationResult

  def evalspc(s: State, es: Seq[ast.Exp], pvef: ast.Exp => PartialVerificationError, v: Verifier, generateChecks: Boolean = true)
           (Q: (State, List[Term], Verifier) => VerificationResult)
           : VerificationResult

  def eval(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
          (Q: (State, Term, Verifier) => VerificationResult)
          : VerificationResult

  def evalpc(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier, generateChecks: Boolean = true)
          (Q: (State, Term, Verifier) => VerificationResult)
          : VerificationResult

  def evalLocationAccess(s: State,
                         locacc: ast.LocationAccess,
                         pve: PartialVerificationError,
                         v: Verifier)
                        (Q: (State, String, Seq[Term], Verifier) => VerificationResult)
                        : VerificationResult

  def evalLocationAccesspc(s: State,
                         locacc: ast.LocationAccess,
                         pve: PartialVerificationError,
                         v: Verifier,
                         generateChecks: Boolean = true)
                        (Q: (State, String, Seq[Term], Verifier) => VerificationResult)
                        : VerificationResult

  def evalQuantified(s: State,
                     quant: Quantifier,
                     vars: Seq[ast.LocalVarDecl],
                     es1: Seq[ast.Exp],
                     es2: Seq[ast.Exp],
                     optTriggers: Option[Seq[ast.Trigger]],
                     name: String,
                     pve: PartialVerificationError,
                     v: Verifier)
                    (Q: (State, Seq[Var], Seq[Term], Seq[Term], Seq[Trigger], (Seq[Quantification], Seq[Quantification]), Verifier) => VerificationResult)
                    : VerificationResult
}

object evaluator extends EvaluationRules with Immutable {
  import consumer._
  import producer._

  def evals(s: State, es: Seq[ast.Exp], pvef: ast.Exp => PartialVerificationError, v: Verifier)
           (Q: (State, List[Term], Verifier) => VerificationResult)
           : VerificationResult =

    evals2(s, es, Nil, pvef, v)(Q)

  def evalspc(s: State, es: Seq[ast.Exp], pvef: ast.Exp => PartialVerificationError, v: Verifier, generateChecks: Boolean = true)
          (Q: (State, List[Term], Verifier) => VerificationResult)
           : VerificationResult =

    evals2pc(s, es, Nil, pvef, v, generateChecks)(Q)

  private def evals2(s: State, es: Seq[ast.Exp], ts: List[Term], pvef: ast.Exp => PartialVerificationError, v: Verifier)
                    (Q: (State, List[Term], Verifier) => VerificationResult)
                    : VerificationResult = {

    if (es.isEmpty)
      Q(s, ts.reverse, v)
    else
      eval(s, es.head, pvef(es.head), v)((s1, t, v1) =>
        evals2(s1, es.tail, t :: ts, pvef, v1)(Q))
  }

  private def evals2pc(s: State, es: Seq[ast.Exp], ts: List[Term], pvef: ast.Exp => PartialVerificationError, v: Verifier, generateChecks: Boolean)
                    (Q: (State, List[Term], Verifier) => VerificationResult)
                    : VerificationResult = {

    if (es.isEmpty)
      Q(s, ts.reverse, v)
    else
      evalpc(s, es.head, pvef(es.head), v, generateChecks)((s1, t, v1) =>
        evals2pc(s1, es.tail, t :: ts, pvef, v1, generateChecks)(Q))
  }

  /** Wrapper Method for eval, for logging. See Executor.scala for explanation of analogue. **/
  @inline
  def eval(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
          (Q: (State, Term, Verifier) => VerificationResult)
          : VerificationResult = {

    val sepIdentifier = SymbExLogger.currentLog().openScope(new EvaluateRecord(e, s, v.decider.pcs))
    eval3(s, e, pve, v)((s1, t, v1) => {
      SymbExLogger.currentLog().closeScope(sepIdentifier)
      Q(s1, t, v1)})
  }

  def evalpc(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier, generateChecks: Boolean = true)
          (Q: (State, Term, Verifier) => VerificationResult)
          : VerificationResult = {

    val sepIdentifier = SymbExLogger.currentLog().openScope(new EvaluatePCRecord(e, s, v.decider.pcs))
    eval3pc(s, e, pve, v, generateChecks)((s1, t, v1) => {
      SymbExLogger.currentLog().closeScope(sepIdentifier)
      Q(s1, t, v1)})
  }

  def eval3(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
           (Q: (State, Term, Verifier) => VerificationResult)
           : VerificationResult = {


    /* For debugging only */
    e match {
      case  _: ast.TrueLit | _: ast.FalseLit | _: ast.NullLit | _: ast.IntLit | _: ast.FullPerm | _: ast.NoPerm
            | _: ast.AbstractLocalVar | _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.Result
            | _: ast.WildcardPerm | _: ast.FieldAccess =>

      case _ =>
        v.logger.debug(s"\nEVAL ${viper.silicon.utils.ast.sourceLineColumn(e)}: $e")
        v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
        if (s.partiallyConsumedHeap.nonEmpty)
          v.logger.debug("pcH = " + s.partiallyConsumedHeap.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
        if (s.reserveHeaps.nonEmpty)
          v.logger.debug("hR = " + s.reserveHeaps.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
        s.oldHeaps.get(Verifier.MAGIC_WAND_LHS_STATE_LABEL) match {
          case Some(hLhs) =>   v.logger.debug("hLhs = " + v.stateFormatter.format(hLhs))
          case None =>
        }
        v.decider.prover.comment(s"[eval] $e")
    }

    /* Switch to the eval heap (σUsed) of magic wand's exhale-ext, if necessary.
     * Also deactivate magic wand's recording of consumed and produced permissions: if the
     * evaluation to perform involves consuming or producing permissions, e.g. because of
     * an unfolding expression, these should not be recorded.
     */
    val s1 = s.copy(h = magicWandSupporter.getEvalHeap(s),
                    reserveHeaps = Nil,
                    exhaleExt = false)

    val s1a = s1.copy(evalHeapsSet = false)

    eval2(s1a, e, pve, v)((s2, t, v1) => {
      val s3 =
        if (s2.recordPossibleTriggers)
          e match {
            case pt: ast.PossibleTrigger =>
              s2.copy(possibleTriggers = s2.possibleTriggers + (pt -> t))
            case fa: ast.FieldAccess if s2.qpFields.contains(fa.field) =>
              s2.copy(possibleTriggers = s2.possibleTriggers + (fa -> t))
            case _ =>
              s2}
        else
          s2
      val s4 = s3.copy(h = s.h,
                       reserveHeaps = s.reserveHeaps,
                       exhaleExt = s.exhaleExt)
      Q(s4, t, v1)})
  }

  def eval3pc(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier, generateChecks: Boolean)
           (Q: (State, Term, Verifier) => VerificationResult)
           : VerificationResult = {


    /* For debugging only */
    e match {
      case  _: ast.TrueLit | _: ast.FalseLit | _: ast.NullLit | _: ast.IntLit | _: ast.FullPerm | _: ast.NoPerm
            | _: ast.AbstractLocalVar | _: ast.WildcardPerm | _: ast.FractionalPerm | _: ast.Result
            | _: ast.WildcardPerm | _: ast.FieldAccess =>

      case _ =>
        v.logger.debug(s"\nEVAL ${viper.silicon.utils.ast.sourceLineColumn(e)}: $e")
        v.logger.debug(v.stateFormatter.format(s, v.decider.pcs))
        if (s.partiallyConsumedHeap.nonEmpty)
          v.logger.debug("pcH = " + s.partiallyConsumedHeap.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
        if (s.reserveHeaps.nonEmpty)
          v.logger.debug("hR = " + s.reserveHeaps.map(v.stateFormatter.format).mkString("", ",\n     ", ""))
        s.oldHeaps.get(Verifier.MAGIC_WAND_LHS_STATE_LABEL) match {
          case Some(hLhs) =>   v.logger.debug("hLhs = " + v.stateFormatter.format(hLhs))
          case None =>
        }
        v.decider.prover.comment(s"[eval] $e")
    }

    /* Switch to the eval heap (σUsed) of magic wand's exhale-ext, if necessary.
     * Also deactivate magic wand's recording of consumed and produced permissions: if the
     * evaluation to perform involves consuming or producing permissions, e.g. because of
     * an unfolding expression, these should not be recorded.
     */
    val s1 = s.copy(h = magicWandSupporter.getEvalHeap(s),
                    reserveHeaps = Nil,
                    exhaleExt = false)

    val s1a = s1.copy(evalHeapsSet = false) // resetting evalHeapsSet to false (only true after evaluating an unfolding expression)

    eval2pc(s1a, e, pve, v, generateChecks)((s2, t, v1) => {
      val s3 =
        if (s2.recordPossibleTriggers)
          e match {
            case pt: ast.PossibleTrigger =>
              s2.copy(possibleTriggers = s2.possibleTriggers + (pt -> t))
            case fa: ast.FieldAccess if s2.qpFields.contains(fa.field) =>
              s2.copy(possibleTriggers = s2.possibleTriggers + (fa -> t))
            case _ =>
              s2}
        else
          s2
      val s4 = s3.copy(h = s.h,
                       reserveHeaps = s.reserveHeaps,
                       exhaleExt = s.exhaleExt)
      Q(s4, t, v1)})
  }

  protected def eval2(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier)
                     (Q: (State, Term, Verifier) => VerificationResult)
                     : VerificationResult = {

    val resultTerm = e match {
      case _: ast.TrueLit => Q(s, True(), v)
      case _: ast.FalseLit => Q(s, False(), v)

      case _: ast.NullLit => Q(s, Null(), v)
      case ast.IntLit(bigval) => Q(s, IntLiteral(bigval), v)

      case ast.EqCmp(e0, e1) => evalBinOp(s, e0, e1, Equals, pve, v)(Q)
      case ast.NeCmp(e0, e1) => evalBinOp(s, e0, e1, (p0: Term, p1: Term) => Not(Equals(p0, p1)), pve, v)(Q)

      case x: ast.AbstractLocalVar => Q(s, s.g(x), v)

      case _: ast.FullPerm => Q(s, FullPerm(), v)
      case _: ast.NoPerm => Q(s, NoPerm(), v)

      case ast.FractionalPerm(e0, e1) =>
        var t1: Term = null
        evalBinOp(s, e0, e1, (t0, _t1) => {t1 = _t1; FractionPerm(t0, t1)}, pve, v)((s1, tFP, v1) =>
          failIfDivByZero(s1, tFP, e1, t1, predef.Zero, pve, v1)(Q))

      /*
      case _: ast.WildcardPerm =>
        val (tVar, tConstraints) = v.decider.freshARP()
        v.decider.assume(tConstraints)
        /* TODO: Only record wildcards in State.constrainableARPs that are used in exhale
         *       position. Currently, wildcards used in inhale position (only) may not be removed
         *       from State.constrainableARPs (potentially inefficient, but should be sound).
         *
         *       Probably better in general: change evaluator signature such that, in addition to
         *       the resulting term, further data about the evaluation process (e.g. a mapping
         *       from expressions to terms, fresh wildcards, ...) is returned.
         *
         *       Alternative (for just wildcards): introduce WildcardPerm, extract them from the
         *       term returned by eval, mark as constrainable on client-side (e.g. in consumer).
         */
        val s1 =
          s.copy(functionRecorder = s.functionRecorder.recordArp(tVar, tConstraints))
           .setConstrainable(Seq(tVar), true)
        Q(s1, tVar, v)
       */

      case fa: ast.FieldAccess => {
        eval(s, fa.rcv, pve, v)((s1, tRcvr, v1) => {
        if (s.qpFields.contains(fa.field)) {
           /* Quantified permissions are not supported by Gradual Viper; this case code is dead. */
           val (relevantChunks, _) =
              quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s1.h, BasicChunkIdentifier(fa.field.name))
            s1.smCache.get((fa.field, relevantChunks)) match {
              case Some((fvfDef: SnapshotMapDefinition, totalPermissions)) if !Verifier.config.disableValueMapCaching() =>
                /* The next assertion must be made if the FVF definition is taken from the cache;
                * in the other case it is part of quantifiedChunkSupporter.withValue.
                */
                /* Re-emit definition since the previous definition could be nested under
                * an auxiliary quantifier (resulting from the evaluation of some Silver
                * quantifier in whose body field 'fa.field' was accessed)
                * which is protected by a trigger term that we currently don't have.
                */
                v1.decider.assume(fvfDef.valueDefinitions)
                val trigger = FieldTrigger(fa.field.name, fvfDef.sm, tRcvr)
                v1.decider.assume(trigger)
                if (s1.triggerExp) {
                  val fvfLookup = Lookup(fa.field.name, fvfDef.sm, tRcvr)
                  val fr1 = s1.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, fvfLookup)
                  val s2 = s1.copy(functionRecorder = fr1)
                  Q(s2, fvfLookup, v1)
                } else {
                  v1.decider.assert(IsPositive(totalPermissions.replace(`?r`, tRcvr))) {
                    case false =>
                      createFailure(pve dueTo InsufficientPermission(fa), v1, s1)
                    case true =>
                      val fvfLookup = Lookup(fa.field.name, fvfDef.sm, tRcvr)
                      val fr1 = s1.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, fvfLookup).recordFvfAndDomain(fvfDef)
                      val s2 = s1.copy(functionRecorder = fr1, possibleTriggers = if (s1.recordPossibleTriggers) s1.possibleTriggers + (fa -> trigger) else s1.possibleTriggers)
                      Q(s2, fvfLookup, v1)}
                }
              case _ =>
                val (smDef1, smCache1) =
                  quantifiedChunkSupporter.summarisingSnapshotMap(
                    s = s1,
                    resource = fa.field,
                    codomainQVars = Seq(`?r`),
                    relevantChunks = relevantChunks,
                    optSmDomainDefinitionCondition =  None,
                    optQVarsInstantiations = None,
                    v = v1)
                val trigger = FieldTrigger(fa.field.name, smDef1.sm, tRcvr)
                v1.decider.assume(trigger)
                val permCheck =
                  if (s1.triggerExp) {
                    True()
                  } else {
                    val totalPermissions = smCache1.get((fa.field, relevantChunks)).get._2
                      /* TODO: Have totalPermissions returned by quantifiedChunkSupporter.summarisingSnapshotMap */
                    IsPositive(totalPermissions.replace(`?r`, tRcvr))
                  }
                v1.decider.assert(permCheck) {
                  case false =>
                    createFailure(pve dueTo InsufficientPermission(fa), v1, s1)
                  case true =>
                    val smLookup = Lookup(fa.field.name, smDef1.sm, tRcvr)
                    val fr2 =
                      s1.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, smLookup)
                                        .recordFvfAndDomain(smDef1)
                    val s2 = s1.copy(functionRecorder = fr2,
                                    smCache = smCache1)
                    Q(s2, smLookup, v1)}
                }
          //})
        } else {
          evalLocationAccess(s, fa, pve, v)((s1, _, tArgs, v1) => {
            val ve = pve dueTo InsufficientPermission(fa)
            val resource = fa.res(Verifier.program)
            val addToOh = true /* so lookup knows whether or not to add optimistically assumed permissions to the optimistic heap */
            chunkSupporter.lookup(s1, s1.h, s1.optimisticHeap, addToOh, resource, fa, tArgs, pve, ve, v1)((s2, h2, oh2, tSnap, v2) => {
              val fr = s2.functionRecorder.recordSnapshot(fa, v2.decider.pcs.branchConditions, tSnap)
              val s3 = s2.copy(h = h2, optimisticHeap = oh2, functionRecorder = fr)
              Q(s3, tSnap, v1)
            })
          })
        }
      })}
      case ast.Not(e0) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          Q(s1, Not(t0), v1))

      case ast.Minus(e0) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          Q(s1, Minus(0, t0), v1))

      /*
      case ast.Old(e0) =>
        evalInOldState(s, Verifier.PRE_STATE_LABEL, e0, pve, v)(Q)

      case old @ ast.LabelledOld(e0, lbl) =>
        s.oldHeaps.get(lbl) match {
          case None =>
            Failure(pve dueTo LabelledStateNotReached(old))
          case _ =>
            evalInOldState(s, lbl, e0, pve, v)(Q)}

      case ast.Let(x, e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          eval(s1.copy(g = s1.g + (x.localVar, t0)), e1, pve, v1)(Q))
      */

      /* Strict evaluation of AND */
      case ast.And(e0, e1) if Verifier.config.disableShortCircuitingEvaluations() =>
        evalBinOp(s, e0, e1, (t1, t2) => And(t1, t2), pve, v)(Q)

      /* Short-circuiting evaluation of AND */
      case ae @ ast.And(_, _) =>
        val flattened = flattenOperator(ae, {case ast.And(e0, e1) => Seq(e0, e1)})
        evalSeqShortCircuit(And, s, flattened, pve, v)(Q)



      /* Strict evaluation of OR */
      case ast.Or(e0, e1) if Verifier.config.disableShortCircuitingEvaluations() =>
        evalBinOp(s, e0, e1, (t1, t2) => Or(t1, t2), pve, v)(Q)

      /* Short-circuiting evaluation of OR */
      case oe @ ast.Or(_, _) =>
        val flattened = flattenOperator(oe, {case ast.Or(e0, e1) => Seq(e0, e1)})
        evalSeqShortCircuit(Or, s, flattened, pve, v)(Q)

      /*
      case implies @ ast.Implies(e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          evalImplies(s1, t0, e1, implies.info == FromShortCircuitingAnd, pve, v1)(Q))

      case ast.CondExp(e0, e1, e2) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          joiner.join[Term, Term](s1, v1)((s2, v2, QB) =>
            brancher.branch(s2, t0, v2)(
              (s3, v3) => eval(s3, e1, pve, v3)(QB),
              (s3, v3) => eval(s3, e2, pve, v3)(QB))
          )(entries => {
            /* TODO: If branch(...) took orElse-continuations that are executed if a branch is dead, then then
                comparisons with t0/Not(t0) wouldn't be necessary. */
            val (s2, result) = entries match {
              case Seq(entry) => // One branch is dead
                (entry.s, entry.data)
              case Seq(entry1, entry2) => // Both branches are alive
                (entry1.s.merge(entry2.s), Ite(t0, entry1.data, entry2.data))
              case _ =>
                sys.error(s"Unexpected join data entries: $entries")}
            (s2, result)
          })(Q))
       */

      /* Integers */

      case ast.Add(e0, e1) =>
        evalBinOp(s, e0, e1, Plus, pve, v)(Q)

      case ast.Sub(e0, e1) =>
        evalBinOp(s, e0, e1, Minus, pve, v)(Q)

      case ast.Mul(e0, e1) =>
        evalBinOp(s, e0, e1, Times, pve, v)(Q)

      case ast.Div(e0, e1) =>
        evalBinOp(s, e0, e1, Div, pve, v)((s1, tDiv, v1) =>
          failIfDivByZero(s1, tDiv, e1, tDiv.p1, 0, pve, v1)(Q))

      case ast.Mod(e0, e1) =>
        evalBinOp(s, e0, e1, Mod, pve, v)((s1, tMod, v1) =>
          failIfDivByZero(s1, tMod, e1, tMod.p1, 0, pve, v1)(Q))

      case ast.LeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtMost, pve, v)(Q)

      case ast.LtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Less, pve, v)(Q)

      case ast.GeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtLeast, pve, v)(Q)

      case ast.GtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Greater, pve, v)(Q)

      /* Permissions */

      case ast.PermAdd(e0, e1) =>
        evalBinOp(s, e0, e1, PermPlus, pve, v)(Q)

      case ast.PermSub(e0, e1) =>
        evalBinOp(s, e0, e1, PermMinus, pve, v)(Q)

      case ast.PermMinus(e0) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          Q(s1, PermMinus(NoPerm(), t0), v1))

      case ast.PermMul(e0, e1) =>
        evalBinOp(s, e0, e1, PermTimes, pve, v)(Q)

      case ast.IntPermMul(e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          eval(s1, e1, pve, v1)((s2, t1, v2) =>
            Q(s2, IntPermTimes(t0, t1), v2)))

      case ast.PermDiv(e0, e1) =>
        eval(s, e0, pve, v)((s1, t0, v1) =>
          eval(s1, e1, pve, v1)((s2, t1, v2) =>
            failIfDivByZero(s2, PermIntDiv(t0, t1), e1, t1, 0, pve, v2)(Q)))

      case ast.PermLeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtMost, pve, v)(Q)

      case ast.PermLtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Less, pve, v)(Q)

      case ast.PermGeCmp(e0, e1) =>
        evalBinOp(s, e0, e1, AtLeast, pve, v)(Q)

      case ast.PermGtCmp(e0, e1) =>
        evalBinOp(s, e0, e1, Greater, pve, v)(Q)

      /* Others */

      /*
      /* Domains not handled directly */
      case dfa @ ast.DomainFuncApp(funcName, eArgs, _) =>
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) => {
          val inSorts = tArgs map (_.sort)
          val outSort = v1.symbolConverter.toSort(dfa.typ)
          val fi = v1.symbolConverter.toFunction(Verifier.program.findDomainFunction(funcName), inSorts :+ outSort)
          Q(s1, App(fi, tArgs), v1)})

      case ast.CurrentPerm(resacc) =>
        val h = s.partiallyConsumedHeap.getOrElse(s.h)
        evalResourceAccess(s, resacc, pve, v)((s1, identifier, args, v1) => {
          val res = resacc.res(Verifier.program)
          /* It is assumed that, for a given field/predicate/wand identifier (res)
           * either only quantified or only non-quantified chunks are used.
           */
          val usesQPChunks = res match {
            case _: ast.MagicWand => s1.qpMagicWands.contains(identifier.asInstanceOf[MagicWandIdentifier])
            case field: ast.Field => s1.qpFields.contains(field)
            case pred: ast.Predicate => s1.qpPredicates.contains(pred)}
          val (s2, currentPermAmount) =
            if (usesQPChunks) {
              res match {
                case wand: ast.MagicWand =>
                  val (relevantChunks, _) =
                    quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](h, identifier)
                  val bodyVars = wand.subexpressionsToEvaluate(Verifier.program)
                  val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v1.symbolConverter.toSort(bodyVars(i).typ)))
                  val (s2, smDef, pmDef) =
                    quantifiedChunkSupporter.heapSummarisingMaps(s1, wand, formalVars, relevantChunks, v1)
                  v1.decider.assume(PredicateTrigger(identifier.toString, smDef.sm, args))
                  (s2, PredicatePermLookup(identifier.toString, pmDef.pm, args))

                case field: ast.Field =>
                  val (relevantChunks, _) =
                    quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](h, identifier)
                  val (s2, smDef, pmDef) =
                    quantifiedChunkSupporter.heapSummarisingMaps(s1, field, Seq(`?r`), relevantChunks, v1)
                  v1.decider.assume(FieldTrigger(field.name, smDef.sm, args.head))
                  val currentPermAmount = PermLookup(field.name, pmDef.pm, args.head)
                  v1.decider.prover.comment(s"perm($resacc)  ~~>  assume upper permission bound")
                  v1.decider.assume(PermAtMost(currentPermAmount, FullPerm()))
                  (s2, currentPermAmount)

                case predicate: ast.Predicate =>
                  val (relevantChunks, _) =
                    quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](h, identifier)
                  val (s2, smDef, pmDef) =
                    quantifiedChunkSupporter.heapSummarisingMaps(
                      s1, predicate, s1.predicateFormalVarMap(predicate), relevantChunks, v1)
                  val trigger = PredicateTrigger(predicate.name, smDef.sm, args)
                  v1.decider.assume(trigger)
                  (s2, PredicatePermLookup(identifier.toString, pmDef.pm, args))
              }
            } else {
              val chs = chunkSupporter.findChunksWithID[NonQuantifiedChunk](h.values, identifier)
              val currentPermAmount =
                chs.foldLeft(NoPerm(): Term)((q, ch) => {
                  val argsPairWiseEqual = And(args.zip(ch.args).map { case (a1, a2) => a1 === a2 })
                  PermPlus(q, Ite(argsPairWiseEqual, ch.perm, NoPerm()))
                })
              /* TODO: See todo above */
//              v1.decider.prover.comment(s"perm($locacc)  ~~>  assume upper permission bound")
//              v1.decider.prover.comment(perm.toString)
//              v1.decider.assume(PermAtMost(perm, FullPerm()))
              (s, currentPermAmount)
            }

          Q(s2, currentPermAmount, v1)})

      case ast.ForPerm(vars, resourceAccess, body) =>

        /* Iterate over the list of relevant chunks in continuation passing style (very similar
         * to evals), and evaluate the forperm-body with a different qvar assignment each time.
        */

        def bindRcvrsAndEvalBody(s: State, chs: Iterable[NonQuantifiedChunk], args: Seq[ast.Exp], ts: Seq[Term], v: Verifier)
                                (Q: (State, Seq[Term], Verifier) => VerificationResult)
                                : VerificationResult = {
          if (chs.isEmpty)
            Q(s, ts.reverse, v)
          else {
            val ch = chs.head

            val rcvrs = ch.args
            val s1 = s.copy()
            var g1 = s1.g
            var addCons : Seq[Term] = Seq()
            for (vr <- vars) {
              if (args.contains(vr.localVar)) {
                val indices = args.zipWithIndex.filter(ai => ai._1 == vr.localVar).map(_._2)
                val index = indices.head
                g1 = g1 + (vr.localVar, rcvrs(index))
                if (indices.length > 1) {
                  val equalArgs = And(indices.tail map { i => rcvrs(i) === rcvrs(index) })
                  addCons = addCons :+ equalArgs
                }
              }
            }
            val s2 = s1.copy(g1)

            val nonQuantArgs = args filter (a => !vars.map(_.localVar).contains(a))
            val indices = nonQuantArgs map (a => args.indexOf(a))

            evals(s2, nonQuantArgs, _ => pve, v)((s3, tArgs, v1) => {
              val argsWithIndex = tArgs zip indices
              val zippedArgs = argsWithIndex map (ai => (ai._1, ch.args(ai._2)))
              val argsPairWiseEqual = And(zippedArgs map {case (a1, a2) => a1 === a2})

              evalImplies(s3, Ite(argsPairWiseEqual, And(addCons :+ IsPositive(ch.perm)), False()), body, false, pve, v1)((s4, tImplies, v2) =>
                bindRcvrsAndEvalBody(s4, chs.tail, args, tImplies +: ts, v2)(Q))
            })
          }
        }

        def bindQuantRcvrsAndEvalBody(s: State, chs: Iterable[QuantifiedBasicChunk], args: Seq[ast.Exp], ts: Seq[Term], v: Verifier)
                                     (Q: (State, Seq[Term], Verifier) => VerificationResult)
                                     : VerificationResult = {
          if (chs.isEmpty)
            Q(s, ts.reverse, v)
          else {
            val ch = chs.head

            val localVars = vars map (_.localVar)
            val tVars = localVars map (x => v.decider.fresh(x.name, v.symbolConverter.toSort(x.typ)))
            val gVars = Store(localVars zip tVars)

            val s1 = s.copy(s.g + gVars, quantifiedVariables = tVars ++ s.quantifiedVariables)

            evals(s1, args, _ => pve, v)((s2, ts1, v1) => {
              val bc = IsPositive(ch.perm.replace(ch.quantifiedVars, ts1))
              val tTriggers = Seq(Trigger(ch.valueAt(ts1)))

              val trig = ch match {
                case fc: QuantifiedFieldChunk => FieldTrigger(fc.id.name, fc.fvf, ts1.head)
                case pc: QuantifiedPredicateChunk => PredicateTrigger(pc.id.name, pc.psf, ts1)
                case wc: QuantifiedMagicWandChunk => PredicateTrigger(wc.id.toString, wc.wsf, ts1)
              }

              evalImplies(s2, And(trig, bc), body, false, pve, v1)((s3, tImplies, v2) => {
                val tQuant = Quantification(Forall, tVars, tImplies, tTriggers)
                bindQuantRcvrsAndEvalBody(s3, chs.tail, args, tQuant +: ts, v2)(Q)})
            })
          }
        }

        val s1 = s.copy(h = s.partiallyConsumedHeap.getOrElse(s.h))

        val resIdent = ChunkIdentifier(resourceAccess.res(Verifier.program), Verifier.program)
        val args = resourceAccess match {
          case fa: ast.FieldAccess => Seq(fa.rcv)
          case pa: ast.PredicateAccess => pa.args
          case w: ast.MagicWand => w.subexpressionsToEvaluate(Verifier.program)
        }
        val usesQPChunks = resourceAccess.res(Verifier.program) match {
          case _: ast.MagicWand => s1.qpMagicWands.contains(resIdent.asInstanceOf[MagicWandIdentifier])
          case field: ast.Field => s1.qpFields.contains(field)
          case pred: ast.Predicate => s1.qpPredicates.contains(pred)
        }

        if (usesQPChunks) {
            val chs = s1.h.values.collect { case ch: QuantifiedBasicChunk if ch.id == resIdent => ch }
            bindQuantRcvrsAndEvalBody(s1, chs, args, Seq.empty, v)((s2, ts, v1) => {
              val s3 = s2.copy(h = s.h, g = s.g)
              Q(s3, And(ts), v1)
            })
        } else {
          val chs = chunkSupporter.findChunksWithID[NonQuantifiedChunk](s1.h.values, resIdent)
          bindRcvrsAndEvalBody(s1, chs, args, Seq.empty, v)((s2, ts, v1) => {
            val s3 = s2.copy(h = s.h, g = s.g)
            Q(s3, And(ts), v1)
          })
        }

      case sourceQuant: ast.QuantifiedExp /*if config.disableLocalEvaluations()*/ =>
        val (eQuant, qantOp, eTriggers) = sourceQuant match {
          case forall: ast.Forall =>
            /* It is expected that quantifiers have already been provided with triggers,
             * either explicitly or by using a trigger generator.
             */
            (forall, Forall, forall.triggers)
          case exists: ast.Exists =>
            (exists, Exists, exists.triggers)
          case _: ast.ForPerm => sys.error(s"Unexpected quantified expression $sourceQuant")
        }

        val body = eQuant.exp
        val name = s"prog.l${viper.silicon.utils.ast.sourceLine(sourceQuant)}"
        evalQuantified(s, qantOp, eQuant.variables, Nil, Seq(body), Some(eTriggers), name, pve, v){
          case (s1, tVars, _, Seq(tBody), tTriggers, (tAuxGlobal, tAux), v1) =>
            val tAuxHeapIndep = tAux.flatMap(v.quantifierSupporter.makeTriggersHeapIndependent(_, v1.decider.fresh))

            val tlqGlobal = tAuxGlobal flatMap (q1 => q1.deepCollect {case q2: Quantification if !q2.existsDefined {case v: Var if q1.vars.contains(v) => } => q2})
            val tlq = tAux flatMap (q1 => q1.deepCollect {case q2: Quantification if !q2.existsDefined {case v: Var if q1.vars.contains(v) => } => q2})

            v1.decider.prover.comment("Nested auxiliary terms: globals (aux)")
            v1.decider.assume(tAuxGlobal)
            v1.decider.prover.comment("Nested auxiliary terms: globals (tlq)")
            v1.decider.assume(tlqGlobal)
            v1.decider.prover.comment("Nested auxiliary terms: non-globals (aux)")
            v1.decider.assume(tAuxHeapIndep/*tAux*/)
            v1.decider.prover.comment("Nested auxiliary terms: non-globals (tlq)")
            v1.decider.assume(tlq)

            val tQuant = Quantification(qantOp, tVars, tBody, tTriggers, name)
            Q(s1, tQuant, v1)}
       */
      // sufficient for the most basic example
      case fapp @ ast.FuncApp(funcName, eArgs) =>
        val func = Verifier.program.findFunction(funcName)
        val s0 = s.copy(hackIssue387DisablePermissionConsumption = Verifier.config.enableMoreCompleteExhale())
        evals2(s0, eArgs, Nil, _ => pve, v)((s1, tArgs, v1) => {
//          bookkeeper.functionApplications += 1
          val joinFunctionArgs = tArgs //++ c2a.quantifiedVariables.filterNot(tArgs.contains)
          /* TODO: Does it matter that the above filterNot does not filter out quantified
           *       variables that are not "raw" function arguments, but instead are used
           *       in an expression that is used as a function argument?
           *       E.g., in
           *         forall i: Int :: fun(i*i)
           *       the above filterNot will not remove i from the list of already
           *       used quantified variables because i does not match i*i.
           *       Hence, the joinedFApp will take two arguments, namely, i*i and i,
           *       although the latter is not necessary.
           */
          joiner.join[Term, Term](s1, v1)((s2, v2, QB) => {
            val pres = func.pres.map(_.transform {
              /* [Malte 2018-08-20] Two examples of the test suite, one of which is the regression
               * for Carbon issue #210, fail if the subsequent code that strips out triggers from
               * exhaled function preconditions, is commented. The code was originally a work-around
               * for Silicon issue #276. Removing triggers from function preconditions is OK-ish
               * because they are consumed (exhaled), i.e. asserted. However, the triggers are
               * also used to internally generated quantifiers, e.g. related to QPs. My hope is that
               * this hack is no longer needed once heap-dependent triggers are supported.
               */
              case q: ast.Forall => q.copy(triggers = Nil)(q.pos, q.info, q.errT)
            })
            /* Formal function arguments are instantiated with the corresponding actual arguments
             * by adding the corresponding bindings to the store. To avoid formals in error messages
             * and to report actuals instead, we have two choices: the first is two attach a reason
             * transformer to the partial verification error, as done below; the second is to attach
             * a node transformer to every formal, as illustrated by NodeBacktranslationTests.scala.
             * The first approach is slightly simpler and suffices here, though.
             */
            val fargs = func.formalArgs.map(_.localVar)
            val formalsToActuals: Map[ast.LocalVar, ast.Exp] = fargs.zip(eArgs)(collection.breakOut)
            val exampleTrafo = CounterexampleTransformer({
              case ce: SiliconCounterexample => ce.withStore(s2.g)
              case ce => ce
            })
            val pvePre =
              ErrorWrapperWithExampleTransformer(PreconditionInAppFalse(fapp).withReasonNodeTransformed(reasonOffendingNode =>
                reasonOffendingNode.replace(formalsToActuals)), exampleTrafo)
            val s3 = s2.copy(g = Store(fargs.zip(tArgs)),
                             recordVisited = true,
                             functionRecorder = s2.functionRecorder.changeDepthBy(+1),
                                /* Temporarily disable the recorder: when recording (to later on
                                 * translate a particular function fun) and a function application
                                 * fapp is hit, then there is no need to record any information
                                 * about assertions from fapp's precondition since the latter is not
                                 * translated as part of the translation of fun.
                                 * Recording such information is even potentially harmful if formals
                                 * are not syntactically replaced by actuals but rather bound to
                                 * them via the store. Consider the following function:
                                 *   function fun(x: Ref)
                                 *     requires foo(x) // foo is another function
                                 *     ...
                                 *   { ... fun(x.next) ...}
                                 * For fun(x)'s precondition, a mapping from foo(x) to a snapshot is
                                 * recorded. When fun(x.next) is hit, its precondition is consumed,
                                 * but without substituting actuals for formals, continuing to
                                 * record mappings would add another mapping from foo(x) (which is
                                 * actually foo(x.next)) to some potentially different snapshot.
                                 * When translating fun(x) to an axiom, the snapshot of foo(x) from
                                 * fun(x)'s precondition will be the branch-condition-dependent join
                                 * of the recorded snapshots - which is wrong (probably only
                                 * incomplete).
                                 */
                             smDomainNeeded = true,
                             forFraming = true)
            consumes(s3, pres, _ => pvePre, v2)((s4, snap, v3) => {
              val s4_1 = s4.copy(forFraming = false)
              val snap1 = snap.convert(sorts.Snap)
              val tFApp = App(v3.symbolConverter.toFunction(func), snap1 :: tArgs)
              val fr5 =
                s4_1.functionRecorder.changeDepthBy(-1)
                                   .recordSnapshot(fapp, v3.decider.pcs.branchConditions, snap1)
              val s5 = s4_1.copy(g = s2.g,
                               h = s2.h,
                               recordVisited = s2.recordVisited,
                               functionRecorder = fr5,
                               smDomainNeeded = s2.smDomainNeeded,
                               hackIssue387DisablePermissionConsumption = s.hackIssue387DisablePermissionConsumption)
              QB(s5, tFApp, v3)})
            /* TODO: The join-function is heap-independent, and it is not obvious how a
             *       joined snapshot could be defined and represented
             */
            })(join(v1.symbolConverter.toSort(func.typ), s"joined_${func.name}", joinFunctionArgs, v1))(Q)})
     

      // UPDATE: eval case never used since unfolding expressions are only allowed in specifications by Gradual C0
      // However, kept here to support unfolding expressions everywhere in gradual viper
      case unfolding @ ast.Unfolding(
              acc @ ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm),
              eIn) =>
        println("WARNING: eval version of unfolding being called - shouldn't happen in gvc0 programs")
        // val gIns = s.g + Store(predicate.formalArgs map (_.localVar) zip eArgs) // copied from unfold in PredicateSupporter, not sure if needed - Priyam
        val predicate = Verifier.program.findPredicate(predicateName)
        if (s.cycles(predicate) < Verifier.config.recursivePredicateUnfoldings()) { // config value is 1
          evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
            eval(s1, ePerm, pve, v1)((s2, tPerm, v2) =>
              v2.decider.assert(IsNonNegative(tPerm)) {
                case true =>
                  joiner.join[Term, Term](s2, v2)((s3, v3, QB) => {
                    val s4 = s3.incCycleCounter(predicate)
                               .copy(recordVisited = true,
                                 forFraming = true)
                      /* [2014-12-10 Malte] The commented code should replace the code following
                       * it, but using it slows down RingBufferRd.sil significantly. The generated
                       * Z3 output looks nearly identical, so my guess is that it is some kind
                       * of triggering problem, probably related to sequences.
                       */
//                      predicateSupporter.unfold(σ, predicate, tArgs, tPerm, pve, c2, pa)((σ1, c3) => {
//                        val c4 = c3.decCycleCounter(predicate)
//                        eval(σ1, eIn, pve, c4)((tIn, c5) =>
//                          QB(tIn, c5))})

                    val hTotal = s4.h + s4.optimisticHeap
                    val predFramed = chunkSupporter.inHeap(hTotal, hTotal.values, predicate, tArgs, v2)

                    consume(s4, acc, pve, v3)((s5, snap, v4) => {
                      val s5_1 = s5.copy(forFraming = false)
                      val fr6 =
                        s5_1.functionRecorder.recordSnapshot(pa, v4.decider.pcs.branchConditions, snap)
                                           .changeDepthBy(+1)
                      val s6 = s5_1.copy(functionRecorder = fr6,
                                       constrainableARPs = s1.constrainableARPs)
                        /* Recording the unfolded predicate's snapshot is necessary in order to create the
                         * additional predicate-based trigger function applications because these are applied
                         * to the function arguments and the predicate snapshot
                         * (see 'predicateTriggers' in FunctionData.scala).
                         */
                      v4.decider.assume(App(Verifier.predicateData(predicate).triggerFunction, snap.convert(terms.sorts.Snap) +: tArgs))
                      val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
                      val s7 = s6.scalePermissionFactor(tPerm)
                      val insg = s7.g + Store(predicate.formalArgs map (_.localVar) zip tArgs)
                      
                      // if-else casing required for setting origin while handling nested origins (outermost unfolding should be origin) - Priyam
                      val s7a = s7.copy(g = insg, unfoldingAstNode = if (s7.unfoldingAstNode == None) Some(unfolding) else s7.unfoldingAstNode, needConditionFramingUnfold = true)

                      // disable origin tracking (for testing purposes)
                      // val s7b = s7a.copy(unfoldingAstNode = None)
                      
                  
                      produce(s7a, toSf(snap), body, pve, v4)((s8, v5) => {
                        val s9 = s8.copy(g = s7.g,
                                         functionRecorder = s8.functionRecorder.changeDepthBy(-1),
                                         recordVisited = s3.recordVisited,
                                         permissionScalingFactor = s6.permissionScalingFactor,
                                         unfoldingAstNode = s7.unfoldingAstNode, needConditionFramingUnfold = false, generateChecks = s7.generateChecks)
                                   .decCycleCounter(predicate)
                        val s10 = stateConsolidator.consolidateIfRetrying(s9, v5)
                        eval(s10, eIn, pve, v5)((s11, eIn1, v6) => {
                          val ch = BasicChunk(PredicateID, BasicChunkIdentifier(predicateName), tArgs, snap.convert(sorts.Snap), tPerm)

                          body match {
                            case impr @ ast.ImpreciseExp(e) =>
                             // adding consumed predicate to OH when it wasn't statically framed before consume
                              val s12 = if (predFramed) s11.copy(h = s2.h, optimisticHeap = s2.optimisticHeap) else s11.copy(h = s2.h, optimisticHeap = s2.optimisticHeap + ch)
                              Q(s12, eIn1, v6)
                            case _ =>
                              // keep OH chunks assumed during evaluation of eIn
                              // Also, adding consumed predicate to OH when it wasn't statically framed before consume
                              val s12 = if (predFramed) s11.copy(h = s2.h, optimisticHeap = s2.optimisticHeap + s11.optimisticHeap) else 
                                                        s11.copy(h = s2.h, optimisticHeap = s2.optimisticHeap + s11.optimisticHeap + ch)
                              Q(s12, eIn1, v6)
                          }
                        })})})
                  })(join(v2.symbolConverter.toSort(eIn.typ), "joined_unfolding", s2.relevantQuantifiedVariables, v2))(Q)
                case false =>
                  createFailure(pve dueTo NegativePermission(ePerm), v2, s2)}))
        } else {
          val unknownValue = v.decider.appliedFresh("recunf", v.symbolConverter.toSort(eIn.typ), s.relevantQuantifiedVariables)
          // v.logger.debug(s"assigning whole expression a symbolic value: ${unknownValue}")
          Q(s, unknownValue, v)
        }


      /*
      case ast.Applying(wand, eIn) =>
        joiner.join[Term, Term](s, v)((s1, v1, QB) =>
          magicWandSupporter.applyWand(s1, wand, pve, v1)((s2, v2) => {
            eval(s2, eIn, pve, v2)(QB)
        }))(join(v.symbolConverter.toSort(eIn.typ), "joined_applying", s.relevantQuantifiedVariables, v))(Q)

      /* Sequences */

      case ast.SeqContains(e0, e1) => evalBinOp(s, e1, e0, SeqIn, pve, v)(Q)
        /* Note the reversed order of the arguments! */

      case ast.SeqIndex(e0, e1) =>
        evals2(s, Seq(e0, e1), Nil, _ => pve, v)({case (s1, Seq(t0, t1), v1) =>
          if (s1.triggerExp) {
            Q(s1, SeqAt(t0, t1), v1)
          } else {
            v1.decider.assert(AtLeast(t1, IntLiteral(0))) {
              case true =>
                v1.decider.assert(Less(t1, SeqLength(t0))) {
                  case true =>
                    Q(s1, SeqAt(t0, t1), v1)
                  case false =>
                    createFailure(pve dueTo SeqIndexExceedsLength(e0, e1), v1, s1)}
              case false =>
                createFailure(pve dueTo SeqIndexNegative(e0, e1), v1, s1)
            }}})

      case ast.SeqAppend(e0, e1) => evalBinOp(s, e0, e1, SeqAppend, pve, v)(Q)
      case ast.SeqDrop(e0, e1) => evalBinOp(s, e0, e1, SeqDrop, pve, v)(Q)
      case ast.SeqTake(e0, e1) => evalBinOp(s, e0, e1, SeqTake, pve, v)(Q)
      case ast.SeqLength(e0) => eval(s, e0, pve, v)((s1, t0, v1) => Q(s1, SeqLength(t0), v1))
      case ast.EmptySeq(typ) => Q(s, SeqNil(v.symbolConverter.toSort(typ)), v)
      case ast.RangeSeq(e0, e1) => evalBinOp(s, e0, e1, SeqRanged, pve, v)(Q)

      case ast.SeqUpdate(e0, e1, e2) =>
        evals2(s, Seq(e0, e1, e2), Nil, _ => pve, v)({ case (s1, Seq(t0, t1, t2), v1) =>
          if (s1.triggerExp) {
            Q(s1, SeqUpdate(t0, t1, t2), v1)
          } else {
            v1.decider.assert(AtLeast(t1, IntLiteral(0))) {
              case true =>
                v1.decider.assert(Less(t1, SeqLength(t0))) {
                  case true =>
                    Q(s1, SeqUpdate(t0, t1, t2), v1)
                  case false =>
                    Failure(pve dueTo SeqIndexExceedsLength(e0, e1))}
              case false =>
                Failure(pve dueTo SeqIndexNegative(e0, e1))
            }
          }
        })

      case ast.ExplicitSeq(es) =>
        evals2(s, es, Nil, _ => pve, v)((s1, tEs, v1) => {
          val tSeq =
            tEs.tail.foldLeft[SeqTerm](SeqSingleton(tEs.head))((tSeq, te) =>
              SeqAppend(tSeq, SeqSingleton(te)))
          v1.decider.assume(SeqLength(tSeq) === IntLiteral(es.size))
          Q(s1, tSeq, v1)})

      /* Sets and multisets */

      case ast.EmptySet(typ) => Q(s, EmptySet(v.symbolConverter.toSort(typ)), v)
      case ast.EmptyMultiset(typ) => Q(s, EmptyMultiset(v.symbolConverter.toSort(typ)), v)

      case ast.ExplicitSet(es) =>
        evals2(s, es, Nil, _ => pve, v)((s1, tEs, v1) => {
          val tSet =
            tEs.tail.foldLeft[SetTerm](SingletonSet(tEs.head))((tSet, te) =>
              SetAdd(tSet, te))
          Q(s1, tSet, v1)})

      case ast.ExplicitMultiset(es) =>
        evals2(s, es, Nil, _ => pve, v)((s1, tEs, v1) => {
          val tMultiset =
            tEs.tail.foldLeft[MultisetTerm](SingletonMultiset(tEs.head))((tMultiset, te) =>
              MultisetAdd(tMultiset, te))
          Q(s1, tMultiset, v1)})

      case ast.AnySetUnion(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetUnion, pve, v)(Q)
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetUnion, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetIntersection(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetIntersection, pve, v)(Q)
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetIntersection, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetSubset(e0, e1) => e0.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetSubset, pve, v)(Q)
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetSubset, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetMinus(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetDifference, pve, v)(Q)
        case _: ast.MultisetType => evalBinOp(s, e0, e1, MultisetDifference, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetContains(e0, e1) => e1.typ match {
        case _: ast.SetType => evalBinOp(s, e0, e1, SetIn, pve, v)(Q)
        case _: ast.MultisetType => evalBinOp(s, e0, e1, (t0, t1) => MultisetCount(t1, t0), pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetCardinality(e0) => e0.typ match {
        case _: ast.SetType => eval(s, e0, pve, v)((s1, t0, v1) => Q(s1, SetCardinality(t0), v1))
        case _: ast.MultisetType => eval(s, e0, pve, v)((s1, t0, v1) => Q(s1, MultisetCardinality(t0), v1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of type %s"
                            .format(e0, e0.getClass.getName, e0.typ))
      }
      */

      /* Unexpected nodes */

      case _: ast.InhaleExhaleExp =>
        Failure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(e))

      case _: ast.Exp =>
        createFailure(createUnexpectedNodeError(e,""), v, s)
    }

    resultTerm
  }

  // eval2pc is copied from eval2, most of the changes are in the field access case
  // Changed all instances of eval to evalpc
  // Commented out eval2's cases for old, labelledold, implies, condition, domain, function, unfolding
  // sequences, multiset, inhale, exhale, applying, quantified expression

  protected def eval2pc(s: State, e: ast.Exp, pve: PartialVerificationError, v: Verifier, generateChecks: Boolean)
                     (Q: (State, Term, Verifier) => VerificationResult)
                     : VerificationResult = {

    val resultTerm = e match {
      case _: ast.TrueLit => Q(s, True(), v)
      case _: ast.FalseLit => Q(s, False(), v)

      case _: ast.NullLit => Q(s, Null(), v)
      case ast.IntLit(bigval) => Q(s, IntLiteral(bigval), v)

      case ast.EqCmp(e0, e1) => evalBinOpPc(s, e0, e1, Equals, pve, v, generateChecks)(Q)
      case ast.NeCmp(e0, e1) => evalBinOpPc(s, e0, e1, (p0: Term, p1: Term) => Not(Equals(p0, p1)), pve, v, generateChecks)(Q)

      case x: ast.AbstractLocalVar => Q(s, s.g(x), v)

      case _: ast.FullPerm => Q(s, FullPerm(), v)
      case _: ast.NoPerm => Q(s, NoPerm(), v)

      case ast.FractionalPerm(e0, e1) =>
        var t1: Term = null
        evalBinOpPc(s, e0, e1, (t0, _t1) => {t1 = _t1; FractionPerm(t0, t1)}, pve, v, generateChecks)((s1, tFP, v1) =>
          failIfDivByZero(s1, tFP, e1, t1, predef.Zero, pve, v1)(Q))

      /*
      case _: ast.WildcardPerm =>
        val (tVar, tConstraints) = v.decider.freshARP()
        v.decider.assume(tConstraints)
        /* TODO: Only record wildcards in State.constrainableARPs that are used in exhale
         *       position. Currently, wildcards used in inhale position (only) may not be removed
         *       from State.constrainableARPs (potentially inefficient, but should be sound).
         *
         *       Probably better in general: change evaluator signature such that, in addition to
         *       the resulting term, further data about the evaluation process (e.g. a mapping
         *       from expressions to terms, fresh wildcards, ...) is returned.
         *
         *       Alternative (for just wildcards): introduce WildcardPerm, extract them from the
         *       term returned by eval, mark as constrainable on client-side (e.g. in consumer).
         */
        val s1 =
          s.copy(functionRecorder = s.functionRecorder.recordArp(tVar, tConstraints))
           .setConstrainable(Seq(tVar), true)
        Q(s1, tVar, v)
       */
      case fa: ast.FieldAccess => {
        evalpc(s, fa.rcv, pve, v, generateChecks)((s1, tRcvr, v1) => {
        if (s.qpFields.contains(fa.field)) {
            /* quantified permissions are not supported in Gradual Viper, this case code is currently dead. */
            val (relevantChunks, _) =
              quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s1.h, BasicChunkIdentifier(fa.field.name))
            s1.smCache.get((fa.field, relevantChunks)) match {
              case Some((fvfDef: SnapshotMapDefinition, totalPermissions)) if !Verifier.config.disableValueMapCaching() =>
                /* The next assertion must be made if the FVF definition is taken from the cache;
                * in the other case it is part of quantifiedChunkSupporter.withValue.
                */
                /* Re-emit definition since the previous definition could be nested under
                * an auxiliary quantifier (resulting from the evaluation of some Silver
                * quantifier in whose body field 'fa.field' was accessed)
                * which is protected by a trigger term that we currently don't have.
                */
                v1.decider.assume(fvfDef.valueDefinitions)
                val trigger = FieldTrigger(fa.field.name, fvfDef.sm, tRcvr)
                v1.decider.assume(trigger)
                if (s1.triggerExp) {
                  val fvfLookup = Lookup(fa.field.name, fvfDef.sm, tRcvr)
                  val fr1 = s1.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, fvfLookup)
                  val s2 = s1.copy(functionRecorder = fr1)
                  Q(s2, fvfLookup, v1)
                } else {
                  v1.decider.assert(IsPositive(totalPermissions.replace(`?r`, tRcvr))) {
                    case false =>
                      createFailure(pve dueTo InsufficientPermission(fa), v1, s1)
                    case true =>
                      val fvfLookup = Lookup(fa.field.name, fvfDef.sm, tRcvr)
                      val fr1 = s1.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, fvfLookup).recordFvfAndDomain(fvfDef)
                      val s2 = s1.copy(functionRecorder = fr1, possibleTriggers = if (s1.recordPossibleTriggers) s1.possibleTriggers + (fa -> trigger) else s1.possibleTriggers)
                      Q(s2, fvfLookup, v1)}
                }
              case _ =>
                val (smDef1, smCache1) =
                  quantifiedChunkSupporter.summarisingSnapshotMap(
                    s = s1,
                    resource = fa.field,
                    codomainQVars = Seq(`?r`),
                    relevantChunks = relevantChunks,
                    optSmDomainDefinitionCondition =  None,
                    optQVarsInstantiations = None,
                    v = v1)
                val trigger = FieldTrigger(fa.field.name, smDef1.sm, tRcvr)
                v1.decider.assume(trigger)
                val permCheck =
                  if (s1.triggerExp) {
                    True()
                  } else {
                    val totalPermissions = smCache1.get((fa.field, relevantChunks)).get._2
                      /* TODO: Have totalPermissions returned by quantifiedChunkSupporter.summarisingSnapshotMap */
                    IsPositive(totalPermissions.replace(`?r`, tRcvr))
                  }
                v1.decider.assert(permCheck) {
                  case false =>
                    createFailure(pve dueTo InsufficientPermission(fa), v1, s1)
                  case true =>
                    val smLookup = Lookup(fa.field.name, smDef1.sm, tRcvr)
                    val fr2 =
                      s1.functionRecorder.recordSnapshot(fa, v1.decider.pcs.branchConditions, smLookup)
                                        .recordFvfAndDomain(smDef1)
                    val s2 = s1.copy(functionRecorder = fr2,
                                    smCache = smCache1)
                    Q(s2, smLookup, v1)}
                }
          //})
        } else {
          evalLocationAccesspc(s, fa, pve, v, generateChecks)((s1, _, tArgs, v1) => {
            val ve = pve dueTo InsufficientPermission(fa)
            val resource = fa.res(Verifier.program)
            val addToOh = false /* so lookup knows whether or not to add optimistically assumed permissions to the optimistic heap */
            // addToOh represents whether we are in eval (true) or eval-pc (false) - Priyam
            
            val s1_0 = s1.copy(madeOptimisticAssumptions = false)

            chunkSupporter.lookup(s1, s1.h, s1.optimisticHeap, addToOh, resource, fa, tArgs, pve, ve, v1, generateChecks)((s2, h2, oh2, tSnap, v2) => {

              if (s2.madeOptimisticAssumptions &&
                s2.needConditionFramingProduce &&
                s2.needConditionFramingUnfold) {

                  // do the framing check
                  
                  v.logger.debug("We are (should be) making a runtime check")

                  val runtimeCheckAstNode: CheckPosition =
                    (s2.methodCallAstNode, s2.foldOrUnfoldAstNode, s2.loopPosition, s2.unfoldingAstNode) match {
                      case (None, None, None, None) => CheckPosition.GenericNode(fa)
                      case (Some(methodCallAstNode), None, None, _) => CheckPosition.GenericNode(methodCallAstNode)
                      case (None, Some(foldOrUnfoldAstNode), None, _) => CheckPosition.GenericNode(foldOrUnfoldAstNode)
                      case (None, None, Some(loopPosition), _) => loopPosition
                      case (None, None, None, Some(unfoldingAstNode)) => CheckPosition.GenericNode(unfoldingAstNode)
                      case _ => sys.error("Conflicting positions found while adding framing runtime check!")
                    }

                  val (g, tH, tOH) = s2.oldStore match { /* Heap/OH part shouldn't be necessary based on currently functionality, but here for safety - JW */
                   case Some(g) => (g, s2.h + s2.oldHeaps(Verifier.PRE_HEAP_LABEL), s2.optimisticHeap + s2.oldHeaps(Verifier.PRE_OPTHEAP_LABEL))
                   case None => (s2.g, s2.h, s2.optimisticHeap)
                  }

                  val astRcvr = new Translator(s2.copy(g = g, h = tH, optimisticHeap = tOH),
                    v2.decider.pcs).translate(tRcvr) match {
                      case None => sys.error("Error translating! Exiting safely.")
                      case Some(translatedReceiver) => translatedReceiver
                    }

                  // we shouldn't check the generateChecks field of the state
                  // here, because it's always going to be false
                  // (since we're in evalpc!)
                  runtimeChecks.addChecks(runtimeCheckAstNode,
                    ast.FieldAccessPredicate(ast.FieldAccess(astRcvr, fa.field)(),
                      ast.FullPerm()())(),
                    viper.silicon.utils.zip3(v.decider.pcs.branchConditionsSemanticAstNodes,
                      v.decider.pcs.branchConditionsAstNodes,
                      v.decider.pcs.branchConditionsOrigins).map(bc => BranchCond(bc._1, bc._2, bc._3)),
                    fa,
                    s.forFraming)
              }
              
              val fr = s2.functionRecorder.recordSnapshot(fa, v2.decider.pcs.branchConditions, tSnap)
              val s3 = s2.copy(h = h2, optimisticHeap = oh2, functionRecorder = fr)
              Q(s3, tSnap, v1)
            })
          })
        }
      })}
      case ast.Not(e0) =>
        evalpc(s, e0, pve, v, generateChecks)((s1, t0, v1) =>
          Q(s1, Not(t0), v1))

      case ast.Minus(e0) =>
        evalpc(s, e0, pve, v, generateChecks)((s1, t0, v1) =>
          Q(s1, Minus(0, t0), v1))

      /*
      case ast.Old(e0) =>
        evalInOldState(s, Verifier.PRE_STATE_LABEL, e0, pve, v)(Q)

      case old @ ast.LabelledOld(e0, lbl) =>
        s.oldHeaps.get(lbl) match {
          case None =>
            Failure(pve dueTo LabelledStateNotReached(old))
          case _ =>
            evalInOldState(s, lbl, e0, pve, v)(Q)}

      case ast.Let(x, e0, e1) =>
        evalpc(s, e0, pve, v)((s1, t0, v1) =>
          evalpc(s1.copy(g = s1.g + (x.localVar, t0)), e1, pve, v1)(Q))
      */

      /* Strict evaluation of AND */
      case ast.And(e0, e1) if Verifier.config.disableShortCircuitingEvaluations() =>
        evalBinOpPc(s, e0, e1, (t1, t2) => And(t1, t2), pve, v, generateChecks)(Q)

      /* Short-circuiting evaluation of AND */
      case ae @ ast.And(e0, e1) =>
        val flattened = flattenOperator(ae, {case ast.And(e2, e3) => Seq(e2, e3)})
        evalSeqShortCircuitPc(And, s, flattened, pve, v, generateChecks)(Q)

      /* Strict evaluation of OR */
      case ast.Or(e0, e1) if Verifier.config.disableShortCircuitingEvaluations() =>
        evalBinOpPc(s, e0, e1, (t1, t2) => Or(t1, t2), pve, v, generateChecks)(Q)

      /* Short-circuiting evaluation of OR */
      case oe @ ast.Or(e0, e1) =>
        val flattened = flattenOperator(oe, {case ast.Or(e2, e3) => Seq(e2, e3)})
        evalSeqShortCircuitPc(Or, s, flattened, pve, v, generateChecks)(Q)

      /*
      case implies @ ast.Implies(e0, e1) =>
        evalpc(s, e0, pve, v)((s1, t0, v1) =>
          evalImplies(s1, t0, e1, implies.info == FromShortCircuitingAnd, pve, v1)(Q))

      case ast.CondExp(e0, e1, e2) =>
        evalpc(s, e0, pve, v)((s1, t0, v1) =>
          joiner.join[Term, Term](s1, v1)((s2, v2, QB) =>
            brancher.branch(s2, t0, v2)(
              (s3, v3) => evalpc(s3, e1, pve, v3)(QB),
              (s3, v3) => evalpc(s3, e2, pve, v3)(QB))
          )(entries => {
            /* TODO: If branch(...) took orElse-continuations that are executed if a branch is dead, then then
                comparisons with t0/Not(t0) wouldn't be necessary. */
            val (s2, result) = entries match {
              case Seq(entry) => // One branch is dead
                (entry.s, entry.data)
              case Seq(entry1, entry2) => // Both branches are alive
                (entry1.s.merge(entry2.s), Ite(t0, entry1.data, entry2.data))
              case _ =>
                sys.error(s"Unexpected join data entries: $entries")}
            (s2, result)
          })(Q))
      */

      /* Integers */

      case ast.Add(e0, e1) =>
        evalBinOpPc(s, e0, e1, Plus, pve, v, generateChecks)(Q)

      case ast.Sub(e0, e1) =>
        evalBinOpPc(s, e0, e1, Minus, pve, v, generateChecks)(Q)

      case ast.Mul(e0, e1) =>
        evalBinOpPc(s, e0, e1, Times, pve, v, generateChecks)(Q)

      case ast.Div(e0, e1) =>
        evalBinOpPc(s, e0, e1, Div, pve, v, generateChecks)((s1, tDiv, v1) =>
          failIfDivByZero(s1, tDiv, e1, tDiv.p1, 0, pve, v1)(Q))

      case ast.Mod(e0, e1) =>
        evalBinOpPc(s, e0, e1, Mod, pve, v, generateChecks)((s1, tMod, v1) =>
          failIfDivByZero(s1, tMod, e1, tMod.p1, 0, pve, v1)(Q))

      case ast.LeCmp(e0, e1) =>
        evalBinOpPc(s, e0, e1, AtMost, pve, v, generateChecks)(Q)

      case ast.LtCmp(e0, e1) =>
        evalBinOpPc(s, e0, e1, Less, pve, v, generateChecks)(Q)

      case ast.GeCmp(e0, e1) =>
        evalBinOpPc(s, e0, e1, AtLeast, pve, v, generateChecks)(Q)

      case ast.GtCmp(e0, e1) =>
        evalBinOpPc(s, e0, e1, Greater, pve, v, generateChecks)(Q)

      /* Permissions */

      case ast.PermAdd(e0, e1) =>
        evalBinOpPc(s, e0, e1, PermPlus, pve, v, generateChecks)(Q)

      case ast.PermSub(e0, e1) =>
        evalBinOpPc(s, e0, e1, PermMinus, pve, v, generateChecks)(Q)

      case ast.PermMinus(e0) =>
        evalpc(s, e0, pve, v, generateChecks)((s1, t0, v1) =>
          Q(s1, PermMinus(NoPerm(), t0), v1))

      case ast.PermMul(e0, e1) =>
        evalBinOpPc(s, e0, e1, PermTimes, pve, v, generateChecks)(Q)

      case ast.IntPermMul(e0, e1) =>
        evalpc(s, e0, pve, v, generateChecks)((s1, t0, v1) =>
          evalpc(s1, e1, pve, v1, generateChecks)((s2, t1, v2) =>
            Q(s2, IntPermTimes(t0, t1), v2)))

      case ast.PermDiv(e0, e1) =>
        evalpc(s, e0, pve, v, generateChecks)((s1, t0, v1) =>
          evalpc(s1, e1, pve, v1, generateChecks)((s2, t1, v2) =>
            failIfDivByZero(s2, PermIntDiv(t0, t1), e1, t1, 0, pve, v2)(Q)))

      case ast.PermLeCmp(e0, e1) =>
        evalBinOpPc(s, e0, e1, AtMost, pve, v, generateChecks)(Q)

      case ast.PermLtCmp(e0, e1) =>
        evalBinOpPc(s, e0, e1, Less, pve, v, generateChecks)(Q)

      case ast.PermGeCmp(e0, e1) =>
        evalBinOpPc(s, e0, e1, AtLeast, pve, v, generateChecks)(Q)

      case ast.PermGtCmp(e0, e1) =>
        evalBinOpPc(s, e0, e1, Greater, pve, v, generateChecks)(Q)

      case unfolding @ ast.Unfolding(
              acc @ ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm),
              eIn) =>
        // val gIns = s.g + Store(predicate.formalArgs map (_.localVar) zip eArgs) // copied from unfold in PredicateSupporter, not sure if needed - Priyam
        val predicate = Verifier.program.findPredicate(predicateName)
        // v.logger.debug(s"unfolding nested expression: ${eIn}")
        //v.logger.debug(s"recursive unfolding depth ${s.cycles(predicate)}")
        if (s.cycles(predicate) < Verifier.config.recursivePredicateUnfoldings()) { // config value is 1
          evalspc(s, eArgs, _ => pve, v, generateChecks)((s1, tArgs, v1) =>
            evalpc(s1, ePerm, pve, v1, generateChecks)((s2, tPerm, v2) =>
              v2.decider.assert(IsNonNegative(tPerm)) {
                case true =>
                  joiner.join[Term, Term](s2, v2)((s3, v3, QB) => {
                    val s4 = s3.incCycleCounter(predicate)
                               .copy(recordVisited = true,
                                 forFraming = true)
                      /* [2014-12-10 Malte] The commented code should replace the code following
                       * it, but using it slows down RingBufferRd.sil significantly. The generated
                       * Z3 output looks nearly identical, so my guess is that it is some kind
                       * of triggering problem, probably related to sequences.
                       */
//                      predicateSupporter.unfold(σ, predicate, tArgs, tPerm, pve, c2, pa)((σ1, c3) => {
//                        val c4 = c3.decCycleCounter(predicate)
//                        eval(σ1, eIn, pve, c4)((tIn, c5) =>
//                          QB(tIn, c5))})
                    val hTotal = s4.h + s4.optimisticHeap
                    val predFramed = chunkSupporter.inHeap(hTotal, hTotal.values, predicate, tArgs, v2)
                    
                    consume(s4, acc, pve, v3)((s5, snap, v4) => {
                      val s5_1 = s5.copy(forFraming = false)
                      val fr6 =
                        s5_1.functionRecorder.recordSnapshot(pa, v4.decider.pcs.branchConditions, snap)
                                           .changeDepthBy(+1)
                      val s6 = s5_1.copy(functionRecorder = fr6,
                                       constrainableARPs = s1.constrainableARPs)
                        /* Recording the unfolded predicate's snapshot is necessary in order to create the
                         * additional predicate-based trigger function applications because these are applied
                         * to the function arguments and the predicate snapshot
                         * (see 'predicateTriggers' in FunctionData.scala).
                         */
                      v4.decider.assume(App(Verifier.predicateData(predicate).triggerFunction, snap.convert(terms.sorts.Snap) +: tArgs))
                      val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
                      val s7 = s6.scalePermissionFactor(tPerm)
                      val insg = s7.g + Store(predicate.formalArgs map (_.localVar) zip tArgs)

                      // if-else casing required for setting origin while handling nested origins (outermost unfolding should be origin) - Priyam
                      // edge case check for framing condition not needed in the context of producing unfolding expression
                      val s7a = s7.copy(g = insg, unfoldingAstNode = if (s7.unfoldingAstNode == None) Some(unfolding) else s7.unfoldingAstNode, needConditionFramingUnfold = s7.generateChecks)


                      // disable origin tracking (for testing purposes)
                      // val s7b = s7a.copy(unfoldingAstNode = None)
                  
                      produce(s7a, toSf(snap), body, pve, v4)((s8, v5) => {
                        val s9 = s8.copy(g = s7.g,
                                         functionRecorder = s8.functionRecorder.changeDepthBy(-1),
                                         recordVisited = s3.recordVisited,
                                         permissionScalingFactor = s6.permissionScalingFactor,
                                         unfoldingAstNode = s7.unfoldingAstNode, needConditionFramingUnfold = false, generateChecks = s7.generateChecks)
                                   .decCycleCounter(predicate)
                        val s10 = stateConsolidator.consolidateIfRetrying(s9, v5)
                        evalpc(s10, eIn, pve, v5, generateChecks)((s11, eIn1, v6) => {
                          
                          val s11a = s11.copy(evalHeapsSet = true, oldHeaps = s11.oldHeaps + (Verifier.EVAL_HEAP_LABEL -> s11.h) + (Verifier.EVAL_OPTHEAP_LABEL -> s11.optimisticHeap)) // needed for translator
                          val ch = BasicChunk(PredicateID, BasicChunkIdentifier(predicateName), tArgs, snap.convert(sorts.Snap), tPerm)
      
                          body match {
                            case impr @ ast.ImpreciseExp(e) =>
                            // adding consumed predicate to OH when it wasn't statically framed before consume
                              val s12 = if (predFramed) s11a.copy(h = s2.h, optimisticHeap = s2.optimisticHeap) else s11a.copy(h = s2.h, optimisticHeap = s2.optimisticHeap + ch) 
                              QB(s12, eIn1, v6)
                            case _ =>
                              // keep OH chunks assumed during evaluation of eIn
                              // Also, adding consumed predicate to OH when it wasn't statically framed before consume
                              val s12 = if (predFramed) s11a.copy(h = s2.h, optimisticHeap = s2.optimisticHeap + s11.optimisticHeap) else 
                                                        s11a.copy(h = s2.h, optimisticHeap = s2.optimisticHeap + s11.optimisticHeap + ch)
                              QB(s12, eIn1, v6)
                          }
                        })})})
                  })(join(v2.symbolConverter.toSort(eIn.typ), "joined_unfolding", s2.relevantQuantifiedVariables, v2))(Q)
                case false =>
                  createFailure(pve dueTo NegativePermission(ePerm), v2, s2)}))
        } else {
          val unknownValue = v.decider.appliedFresh("recunf", v.symbolConverter.toSort(eIn.typ), s.relevantQuantifiedVariables)
          // v.logger.debug(s"assigning whole expression a symbolic value: ${unknownValue}")
          Q(s, unknownValue, v)
        }


      case fapp @ ast.FuncApp(funcName, eArgs) =>
        val func = Verifier.program.findFunction(funcName)
        val s0 = s.copy(hackIssue387DisablePermissionConsumption = Verifier.config.enableMoreCompleteExhale())
        evals2pc(s0, eArgs, Nil, _ => pve, v, false)((s1, tArgs, v1) => {
//          bookkeeper.functionApplications += 1
          val joinFunctionArgs = tArgs //++ c2a.quantifiedVariables.filterNot(tArgs.contains)
          /* TODO: Does it matter that the above filterNot does not filter out quantified
           *       variables that are not "raw" function arguments, but instead are used
           *       in an expression that is used as a function argument?
           *       E.g., in
           *         forall i: Int :: fun(i*i)
           *       the above filterNot will not remove i from the list of already
           *       used quantified variables because i does not match i*i.
           *       Hence, the joinedFApp will take two arguments, namely, i*i and i,
           *       although the latter is not necessary.
           */
          joiner.join[Term, Term](s1, v1)((s2, v2, QB) => {
            val pres = func.pres.map(_.transform {
              /* [Malte 2018-08-20] Two examples of the test suite, one of which is the regression
               * for Carbon issue #210, fail if the subsequent code that strips out triggers from
               * exhaled function preconditions, is commented. The code was originally a work-around
               * for Silicon issue #276. Removing triggers from function preconditions is OK-ish
               * because they are consumed (exhaled), i.e. asserted. However, the triggers are
               * also used to internally generated quantifiers, e.g. related to QPs. My hope is that
               * this hack is no longer needed once heap-dependent triggers are supported.
               */
              case q: ast.Forall => q.copy(triggers = Nil)(q.pos, q.info, q.errT)
            })
            /* Formal function arguments are instantiated with the corresponding actual arguments
             * by adding the corresponding bindings to the store. To avoid formals in error messages
             * and to report actuals instead, we have two choices: the first is two attach a reason
             * transformer to the partial verification error, as done below; the second is to attach
             * a node transformer to every formal, as illustrated by NodeBacktranslationTests.scala.
             * The first approach is slightly simpler and suffices here, though.
             */
            val fargs = func.formalArgs.map(_.localVar)
            val formalsToActuals: Map[ast.LocalVar, ast.Exp] = fargs.zip(eArgs)(collection.breakOut)
            val exampleTrafo = CounterexampleTransformer({
              case ce: SiliconCounterexample => ce.withStore(s2.g)
              case ce => ce
            })
            val pvePre =
              ErrorWrapperWithExampleTransformer(PreconditionInAppFalse(fapp).withReasonNodeTransformed(reasonOffendingNode =>
                reasonOffendingNode.replace(formalsToActuals)), exampleTrafo)
            val s3 = s2.copy(g = Store(fargs.zip(tArgs)),
                             recordVisited = true,
                             functionRecorder = s2.functionRecorder.changeDepthBy(+1),
                                /* Temporarily disable the recorder: when recording (to later on
                                 * translate a particular function fun) and a function application
                                 * fapp is hit, then there is no need to record any information
                                 * about assertions from fapp's precondition since the latter is not
                                 * translated as part of the translation of fun.
                                 * Recording such information is even potentially harmful if formals
                                 * are not syntactically replaced by actuals but rather bound to
                                 * them via the store. Consider the following function:
                                 *   function fun(x: Ref)
                                 *     requires foo(x) // foo is another function
                                 *     ...
                                 *   { ... fun(x.next) ...}
                                 * For fun(x)'s precondition, a mapping from foo(x) to a snapshot is
                                 * recorded. When fun(x.next) is hit, its precondition is consumed,
                                 * but without substituting actuals for formals, continuing to
                                 * record mappings would add another mapping from foo(x) (which is
                                 * actually foo(x.next)) to some potentially different snapshot.
                                 * When translating fun(x) to an axiom, the snapshot of foo(x) from
                                 * fun(x)'s precondition will be the branch-condition-dependent join
                                 * of the recorded snapshots - which is wrong (probably only
                                 * incomplete).
                                 */
                             smDomainNeeded = true,
                             forFraming = true)
            consumes(s3, pres, _ => pvePre, v2)((s4, snap, v3) => {
              
              val s4_1 = s4.copy(forFraming = false)

              val snap1 = snap.convert(sorts.Snap)
              val tFApp = App(v3.symbolConverter.toFunction(func), snap1 :: tArgs)
              val fr5 =
                s4_1.functionRecorder.changeDepthBy(-1)
                  .recordSnapshot(fapp, v3.decider.pcs.branchConditions, snap1)
              val s5 = s4_1.copy(g = s2.g,
                               h = s2.h,
                               recordVisited = s2.recordVisited,
                               functionRecorder = fr5,
                               smDomainNeeded = s2.smDomainNeeded,
                               hackIssue387DisablePermissionConsumption = s.hackIssue387DisablePermissionConsumption)
              QB(s5, tFApp, v3)})
            /* TODO: The join-function is heap-independent, and it is not obvious how a
             *       joined snapshot could be defined and represented
             */
            })(join(v1.symbolConverter.toSort(func.typ), s"joined_${func.name}", joinFunctionArgs, v1))(Q)})


      /* Others */

      /*
      /* Domains not handled directly */
      case dfa @ ast.DomainFuncApp(funcName, eArgs, _) =>
        evalspc(s, eArgs, _ => pve, v)((s1, tArgs, v1) => {
          val inSorts = tArgs map (_.sort)
          val outSort = v1.symbolConverter.toSort(dfa.typ)
          val fi = v1.symbolConverter.toFunction(Verifier.program.findDomainFunction(funcName), inSorts :+ outSort)
          Q(s1, App(fi, tArgs), v1)})

      case ast.CurrentPerm(resacc) =>
        val h = s.partiallyConsumedHeap.getOrElse(s.h)
        evalResourceAccess(s, resacc, pve, v)((s1, identifier, args, v1) => {
          val res = resacc.res(Verifier.program)
          /* It is assumed that, for a given field/predicate/wand identifier (res)
           * either only quantified or only non-quantified chunks are used.
           */
          val usesQPChunks = res match {
            case _: ast.MagicWand => s1.qpMagicWands.contains(identifier.asInstanceOf[MagicWandIdentifier])
            case field: ast.Field => s1.qpFields.contains(field)
            case pred: ast.Predicate => s1.qpPredicates.contains(pred)}
          val (s2, currentPermAmount) =
            if (usesQPChunks) {
              res match {
                case wand: ast.MagicWand =>
                  val (relevantChunks, _) =
                    quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](h, identifier)
                  val bodyVars = wand.subexpressionsToEvaluate(Verifier.program)
                  val formalVars = bodyVars.indices.toList.map(i => Var(Identifier(s"x$i"), v1.symbolConverter.toSort(bodyVars(i).typ)))
                  val (s2, smDef, pmDef) =
                    quantifiedChunkSupporter.heapSummarisingMaps(s1, wand, formalVars, relevantChunks, v1)
                  v1.decider.assume(PredicateTrigger(identifier.toString, smDef.sm, args))
                  (s2, PredicatePermLookup(identifier.toString, pmDef.pm, args))

                case field: ast.Field =>
                  val (relevantChunks, _) =
                    quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](h, identifier)
                  val (s2, smDef, pmDef) =
                    quantifiedChunkSupporter.heapSummarisingMaps(s1, field, Seq(`?r`), relevantChunks, v1)
                  v1.decider.assume(FieldTrigger(field.name, smDef.sm, args.head))
                  val currentPermAmount = PermLookup(field.name, pmDef.pm, args.head)
                  v1.decider.prover.comment(s"perm($resacc)  ~~>  assume upper permission bound")
                  v1.decider.assume(PermAtMost(currentPermAmount, FullPerm()))
                  (s2, currentPermAmount)

                case predicate: ast.Predicate =>
                  val (relevantChunks, _) =
                    quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](h, identifier)
                  val (s2, smDef, pmDef) =
                    quantifiedChunkSupporter.heapSummarisingMaps(
                      s1, predicate, s1.predicateFormalVarMap(predicate), relevantChunks, v1)
                  val trigger = PredicateTrigger(predicate.name, smDef.sm, args)
                  v1.decider.assume(trigger)
                  (s2, PredicatePermLookup(identifier.toString, pmDef.pm, args))
              }
            } else {
              val chs = chunkSupporter.findChunksWithID[NonQuantifiedChunk](h.values, identifier)
              val currentPermAmount =
                chs.foldLeft(NoPerm(): Term)((q, ch) => {
                  val argsPairWiseEqual = And(args.zip(ch.args).map { case (a1, a2) => a1 === a2 })
                  PermPlus(q, Ite(argsPairWiseEqual, ch.perm, NoPerm()))
                })
              /* TODO: See todo above */
//              v1.decider.prover.comment(s"perm($locacc)  ~~>  assume upper permission bound")
//              v1.decider.prover.comment(perm.toString)
//              v1.decider.assume(PermAtMost(perm, FullPerm()))
              (s, currentPermAmount)
            }

          Q(s2, currentPermAmount, v1)})

      case ast.ForPerm(vars, resourceAccess, body) =>

        /* Iterate over the list of relevant chunks in continuation passing style (very similar
         * to evals), and evaluate the forperm-body with a different qvar assignment each time.
        */

        def bindRcvrsAndEvalBody(s: State, chs: Iterable[NonQuantifiedChunk], args: Seq[ast.Exp], ts: Seq[Term], v: Verifier)
                                (Q: (State, Seq[Term], Verifier) => VerificationResult)
                                : VerificationResult = {
          if (chs.isEmpty)
            Q(s, ts.reverse, v)
          else {
            val ch = chs.head

            val rcvrs = ch.args
            val s1 = s.copy()
            var g1 = s1.g
            var addCons : Seq[Term] = Seq()
            for (vr <- vars) {
              if (args.contains(vr.localVar)) {
                val indices = args.zipWithIndex.filter(ai => ai._1 == vr.localVar).map(_._2)
                val index = indices.head
                g1 = g1 + (vr.localVar, rcvrs(index))
                if (indices.length > 1) {
                  val equalArgs = And(indices.tail map { i => rcvrs(i) === rcvrs(index) })
                  addCons = addCons :+ equalArgs
                }
              }
            }
            val s2 = s1.copy(g1)

            val nonQuantArgs = args filter (a => !vars.map(_.localVar).contains(a))
            val indices = nonQuantArgs map (a => args.indexOf(a))

            evalspc(s2, nonQuantArgs, _ => pve, v)((s3, tArgs, v1) => {
              val argsWithIndex = tArgs zip indices
              val zippedArgs = argsWithIndex map (ai => (ai._1, ch.args(ai._2)))
              val argsPairWiseEqual = And(zippedArgs map {case (a1, a2) => a1 === a2})

              evalImplies(s3, Ite(argsPairWiseEqual, And(addCons :+ IsPositive(ch.perm)), False()), body, false, pve, v1)((s4, tImplies, v2) =>
                bindRcvrsAndEvalBody(s4, chs.tail, args, tImplies +: ts, v2)(Q))
            })
          }
        }


        def bindQuantRcvrsAndEvalBody(s: State, chs: Iterable[QuantifiedBasicChunk], args: Seq[ast.Exp], ts: Seq[Term], v: Verifier)
                                     (Q: (State, Seq[Term], Verifier) => VerificationResult)
                                     : VerificationResult = {
          if (chs.isEmpty)
            Q(s, ts.reverse, v)
          else {
            val ch = chs.head

            val localVars = vars map (_.localVar)
            val tVars = localVars map (x => v.decider.fresh(x.name, v.symbolConverter.toSort(x.typ)))
            val gVars = Store(localVars zip tVars)

            val s1 = s.copy(s.g + gVars, quantifiedVariables = tVars ++ s.quantifiedVariables)

            evalspc(s1, args, _ => pve, v)((s2, ts1, v1) => {
              val bc = IsPositive(ch.perm.replace(ch.quantifiedVars, ts1))
              val tTriggers = Seq(Trigger(ch.valueAt(ts1)))

              val trig = ch match {
                case fc: QuantifiedFieldChunk => FieldTrigger(fc.id.name, fc.fvf, ts1.head)
                case pc: QuantifiedPredicateChunk => PredicateTrigger(pc.id.name, pc.psf, ts1)
                case wc: QuantifiedMagicWandChunk => PredicateTrigger(wc.id.toString, wc.wsf, ts1)
              }

              evalImplies(s2, And(trig, bc), body, false, pve, v1)((s3, tImplies, v2) => {
                val tQuant = Quantification(Forall, tVars, tImplies, tTriggers)
                bindQuantRcvrsAndEvalBody(s3, chs.tail, args, tQuant +: ts, v2)(Q)})
            })
          }
        }

        val s1 = s.copy(h = s.partiallyConsumedHeap.getOrElse(s.h))

        val resIdent = ChunkIdentifier(resourceAccess.res(Verifier.program), Verifier.program)
        val args = resourceAccess match {
          case fa: ast.FieldAccess => Seq(fa.rcv)
          case pa: ast.PredicateAccess => pa.args
          case w: ast.MagicWand => w.subexpressionsToEvaluate(Verifier.program)
        }
        val usesQPChunks = resourceAccess.res(Verifier.program) match {
          case _: ast.MagicWand => s1.qpMagicWands.contains(resIdent.asInstanceOf[MagicWandIdentifier])
          case field: ast.Field => s1.qpFields.contains(field)
          case pred: ast.Predicate => s1.qpPredicates.contains(pred)
        }

        if (usesQPChunks) {
            val chs = s1.h.values.collect { case ch: QuantifiedBasicChunk if ch.id == resIdent => ch }
            bindQuantRcvrsAndEvalBody(s1, chs, args, Seq.empty, v)((s2, ts, v1) => {
              val s3 = s2.copy(h = s.h, g = s.g)
              Q(s3, And(ts), v1)
            })
        } else {
          val chs = chunkSupporter.findChunksWithID[NonQuantifiedChunk](s1.h.values, resIdent)
          bindRcvrsAndEvalBody(s1, chs, args, Seq.empty, v)((s2, ts, v1) => {
            val s3 = s2.copy(h = s.h, g = s.g)
            Q(s3, And(ts), v1)
          })
        }

      case sourceQuant: ast.QuantifiedExp /*if config.disableLocalEvaluations()*/ =>
        val (eQuant, qantOp, eTriggers) = sourceQuant match {
          case forall: ast.Forall =>
            /* It is expected that quantifiers have already been provided with triggers,
             * either explicitly or by using a trigger generator.
             */
            (forall, Forall, forall.triggers)
          case exists: ast.Exists =>
            (exists, Exists, exists.triggers)
          case _: ast.ForPerm => sys.error(s"Unexpected quantified expression $sourceQuant")
        }

        val body = eQuant.exp
        val name = s"prog.l${viper.silicon.utils.ast.sourceLine(sourceQuant)}"
        evalQuantified(s, qantOp, eQuant.variables, Nil, Seq(body), Some(eTriggers), name, pve, v){
          case (s1, tVars, _, Seq(tBody), tTriggers, (tAuxGlobal, tAux), v1) =>
            val tAuxHeapIndep = tAux.flatMap(v.quantifierSupporter.makeTriggersHeapIndependent(_, v1.decider.fresh))

            val tlqGlobal = tAuxGlobal flatMap (q1 => q1.deepCollect {case q2: Quantification if !q2.existsDefined {case v: Var if q1.vars.contains(v) => } => q2})
            val tlq = tAux flatMap (q1 => q1.deepCollect {case q2: Quantification if !q2.existsDefined {case v: Var if q1.vars.contains(v) => } => q2})

            v1.decider.prover.comment("Nested auxiliary terms: globals (aux)")
            v1.decider.assume(tAuxGlobal)
            v1.decider.prover.comment("Nested auxiliary terms: globals (tlq)")
            v1.decider.assume(tlqGlobal)
            v1.decider.prover.comment("Nested auxiliary terms: non-globals (aux)")
            v1.decider.assume(tAuxHeapIndep/*tAux*/)
            v1.decider.prover.comment("Nested auxiliary terms: non-globals (tlq)")
            v1.decider.assume(tlq)

            val tQuant = Quantification(qantOp, tVars, tBody, tTriggers, name)
            Q(s1, tQuant, v1)}


      case ast.Unfolding(
              acc @ ast.PredicateAccessPredicate(pa @ ast.PredicateAccess(eArgs, predicateName), ePerm),
              eIn) =>

        val predicate = Verifier.program.findPredicate(predicateName)
        if (s.cycles(predicate) < Verifier.config.recursivePredicateUnfoldings()) {
          evalspc(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
            evalpc(s1, ePerm, pve, v1)((s2, tPerm, v2) =>
              v2.decider.assert(IsNonNegative(tPerm)) {
                case true =>
                  joiner.join[Term, Term](s2, v2)((s3, v3, QB) => {
                    val s4 = s3.incCycleCounter(predicate)
                               .copy(recordVisited = true
                                 forFraming = true)
                      /* [2014-12-10 Malte] The commented code should replace the code following
                       * it, but using it slows down RingBufferRd.sil significantly. The generated
                       * Z3 output looks nearly identical, so my guess is that it is some kind
                       * of triggering problem, probably related to sequences.
                       */
//                      predicateSupporter.unfold(σ, predicate, tArgs, tPerm, pve, c2, pa)((σ1, c3) => {
//                        val c4 = c3.decCycleCounter(predicate)
//                        eval(σ1, eIn, pve, c4)((tIn, c5) =>
//                          QB(tIn, c5))})
                    consume(s4, acc, pve, v3)((s5, snap, v4) => {

                      val s5_1 = s5.copy(forFraming = false)

                      val fr6 =
                        s5_1.functionRecorder.recordSnapshot(pa, v4.decider.pcs.branchConditions, snap)
                                           .changeDepthBy(+1)
                      val s6 = s5_1.copy(functionRecorder = fr6,
                                       constrainableARPs = s1.constrainableARPs)
                        /* Recording the unfolded predicate's snapshot is necessary in order to create the
                         * additional predicate-based trigger function applications because these are applied
                         * to the function arguments and the predicate snapshot
                         * (see 'predicateTriggers' in FunctionData.scala).
                         */
                      v4.decider.assume(App(Verifier.predicateData(predicate).triggerFunction, snap.convert(terms.sorts.Snap) +: tArgs))
                      val body = predicate.body.get /* Only non-abstract predicates can be unfolded */
                      val s7 = s6.scalePermissionFactor(tPerm)
                      val insg = s7.g + Store(predicate.formalArgs map (_.localVar) zip tArgs)
                      val s7a = s7.copy(g = insg)
                      produce(s7a, toSf(snap), body, pve, v4)((s8, v5) => {
                        val s9 = s8.copy(g = s7.g,
                                         functionRecorder = s8.functionRecorder.changeDepthBy(-1),
                                         recordVisited = s3.recordVisited,
                                         permissionScalingFactor = s6.permissionScalingFactor)
                                   .decCycleCounter(predicate)
                        val s10 = stateConsolidator.consolidateIfRetrying(s9, v5)
                        evalpc(s10, eIn, pve, v5)(QB)})})
                  })(join(v2.symbolConverter.toSort(eIn.typ), "joined_unfolding", s2.relevantQuantifiedVariables, v2))(Q)
                case false =>
                  createFailure(pve dueTo NegativePermission(ePerm), v2, s2)}))
        } else {
          val unknownValue = v.decider.appliedFresh("recunf", v.symbolConverter.toSort(eIn.typ), s.relevantQuantifiedVariables)
          Q(s, unknownValue, v)
        }

      case ast.Applying(wand, eIn) =>
        joiner.join[Term, Term](s, v)((s1, v1, QB) =>
          magicWandSupporter.applyWand(s1, wand, pve, v1)((s2, v2) => {
            evalpc(s2, eIn, pve, v2)(QB)
        }))(join(v.symbolConverter.toSort(eIn.typ), "joined_applying", s.relevantQuantifiedVariables, v))(Q)

      /* Sequences */

      case ast.SeqContains(e0, e1) => evalBinOpPc(s, e1, e0, SeqIn, pve, v)(Q)
        /* Note the reversed order of the arguments! */

      case ast.SeqIndex(e0, e1) =>
        evals2pc(s, Seq(e0, e1), Nil, _ => pve, v)({case (s1, Seq(t0, t1), v1) =>
          if (s1.triggerExp) {
            Q(s1, SeqAt(t0, t1), v1)
          } else {
            v1.decider.assert(AtLeast(t1, IntLiteral(0))) {
              case true =>
                v1.decider.assert(Less(t1, SeqLength(t0))) {
                  case true =>
                    Q(s1, SeqAt(t0, t1), v1)
                  case false =>
                    createFailure(pve dueTo SeqIndexExceedsLength(e0, e1), v1, s1)}
              case false =>
                createFailure(pve dueTo SeqIndexNegative(e0, e1), v1, s1)
            }}})

      case ast.SeqAppend(e0, e1) => evalBinOpPc(s, e0, e1, SeqAppend, pve, v)(Q)
      case ast.SeqDrop(e0, e1) => evalBinOpPc(s, e0, e1, SeqDrop, pve, v)(Q)
      case ast.SeqTake(e0, e1) => evalBinOpPc(s, e0, e1, SeqTake, pve, v)(Q)
      case ast.SeqLength(e0) => evalpc(s, e0, pve, v)((s1, t0, v1) => Q(s1, SeqLength(t0), v1))
      case ast.EmptySeq(typ) => Q(s, SeqNil(v.symbolConverter.toSort(typ)), v)
      case ast.RangeSeq(e0, e1) => evalBinOpPc(s, e0, e1, SeqRanged, pve, v)(Q)

      case ast.SeqUpdate(e0, e1, e2) =>
        evals2pc(s, Seq(e0, e1, e2), Nil, _ => pve, v)({ case (s1, Seq(t0, t1, t2), v1) =>
          if (s1.triggerExp) {
            Q(s1, SeqUpdate(t0, t1, t2), v1)
          } else {
            v1.decider.assert(AtLeast(t1, IntLiteral(0))) {
              case true =>
                v1.decider.assert(Less(t1, SeqLength(t0))) {
                  case true =>
                    Q(s1, SeqUpdate(t0, t1, t2), v1)
                  case false =>
                    Failure(pve dueTo SeqIndexExceedsLength(e0, e1))}
              case false =>
                Failure(pve dueTo SeqIndexNegative(e0, e1))
            }
          }
        })

      case ast.ExplicitSeq(es) =>
        evals2pc(s, es, Nil, _ => pve, v)((s1, tEs, v1) => {
          val tSeq =
            tEs.tail.foldLeft[SeqTerm](SeqSingleton(tEs.head))((tSeq, te) =>
              SeqAppend(tSeq, SeqSingleton(te)))
          v1.decider.assume(SeqLength(tSeq) === IntLiteral(es.size))
          Q(s1, tSeq, v1)})

      /* Sets and multisets */

      case ast.EmptySet(typ) => Q(s, EmptySet(v.symbolConverter.toSort(typ)), v)
      //case ast.EmptyMultiset(typ) => Q(s, EmptyMultiset(v.symbolConverter.toSort(typ)), v)

      case ast.ExplicitSet(es) =>
        evals2pc(s, es, Nil, _ => pve, v)((s1, tEs, v1) => {
          val tSet =
            tEs.tail.foldLeft[SetTerm](SingletonSet(tEs.head))((tSet, te) =>
              SetAdd(tSet, te))
          Q(s1, tSet, v1)})

      case ast.ExplicitMultiset(es) =>
        evals2pc(s, es, Nil, _ => pve, v)((s1, tEs, v1) => {
          val tMultiset =
            tEs.tail.foldLeft[MultisetTerm](SingletonMultiset(tEs.head))((tMultiset, te) =>
              MultisetAdd(tMultiset, te))
          Q(s1, tMultiset, v1)})

      case ast.AnySetUnion(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOpPc(s, e0, e1, SetUnion, pve, v)(Q)
        //case _: ast.MultisetType => evalBinOpPc(s, e0, e1, MultisetUnion, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetIntersection(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOpPc(s, e0, e1, SetIntersection, pve, v)(Q)
        //case _: ast.MultisetType => evalBinOpPc(s, e0, e1, MultisetIntersection, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetSubset(e0, e1) => e0.typ match {
        case _: ast.SetType => evalBinOpPc(s, e0, e1, SetSubset, pve, v)(Q)
        //case _: ast.MultisetType => evalBinOpPc(s, e0, e1, MultisetSubset, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetMinus(e0, e1) => e.typ match {
        case _: ast.SetType => evalBinOpPc(s, e0, e1, SetDifference, pve, v)(Q)
        //case _: ast.MultisetType => evalBinOpPc(s, e0, e1, MultisetDifference, pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetContains(e0, e1) => e1.typ match {
        case _: ast.SetType => evalBinOpPc(s, e0, e1, SetIn, pve, v)(Q)
        //case _: ast.MultisetType => evalBinOpPc(s, e0, e1, (t0, t1) => MultisetCount(t1, t0), pve, v)(Q)
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of sort %s"
                            .format(e, e.getClass.getName, e.typ))
      }

      case ast.AnySetCardinality(e0) => e0.typ match {
        case _: ast.SetType => evalpc(s, e0, pve, v)((s1, t0, v1) => Q(s1, SetCardinality(t0), v1))
        //case _: ast.MultisetType => evalpc(s, e0, pve, v)((s1, t0, v1) => Q(s1, MultisetCardinality(t0), v1))
        case _ => sys.error("Expected a (multi)set-typed expression but found %s (%s) of type %s"
                            .format(e0, e0.getClass.getName, e0.typ))
      }
      */

      /* Unexpected nodes */

      /*
      case _: ast.InhaleExhaleExp =>
        Failure(viper.silicon.utils.consistency.createUnexpectedInhaleExhaleExpressionError(e))
      */
    }

    resultTerm
  }

  def evalQuantified(s: State,
                     quant: Quantifier,
                     vars: Seq[ast.LocalVarDecl],
                     es1: Seq[ast.Exp], /* Are evaluated and added as path conditions before ...*/
                     es2: Seq[ast.Exp], /* ... these terms are evaluated */
                     optTriggers: Option[Seq[ast.Trigger]],
                     name: String,
                     pve: PartialVerificationError,
                     v: Verifier)
                    (Q: (State, Seq[Var], Seq[Term], Seq[Term], Seq[Trigger], (Seq[Quantification], Seq[Quantification]), Verifier) => VerificationResult)
                    : VerificationResult = {

    val localVars = vars map (_.localVar)

    val tVars = localVars map (x => v.decider.fresh(x.name, v.symbolConverter.toSort(x.typ)))
    val gVars = Store(localVars zip tVars)
    val s1 = s.copy(g = s.g + gVars,
                    quantifiedVariables = tVars ++ s.quantifiedVariables,
                    recordPossibleTriggers = true,
                    possibleTriggers = Map.empty) // TODO: Why reset possibleTriggers if they are merged with s.possibleTriggers later anyway?
    type R = (State, Seq[Term], Seq[Term], Seq[Trigger], (Seq[Quantification], Seq[Quantification]), Map[ast.Exp, Term])
    executionFlowController.locallyWithResult[R](s1, v)((s2, v1, QB) => {
       val preMark = v1.decider.setPathConditionMark()
      evals(s2, es1, _ => pve, v1)((s3, ts1, v2) => {
        val bc = And(ts1)
        // we call conjunctExps here to translate the Anded term to its
        // equivalent ast form
        v2.decider.setCurrentBranchCondition(bc, conjunctExps(es1), conjunctExps(es1), None)
        evals(s3, es2, _ => pve, v2)((s4, ts2, v3) => {
          evalTriggers(s4, optTriggers.getOrElse(Nil), pve, v3)((s5, tTriggers, v4) => { // TODO: v4 isn't forward - problem?
            val (auxGlobalQuants, auxNonGlobalQuants) =
              v3.decider.pcs.after(preMark).quantified(quant, tVars, tTriggers, s"$name-aux", isGlobal = false, bc)
            val additionalPossibleTriggers: Map[ast.Exp, Term] =
              if (s.recordPossibleTriggers) s5.possibleTriggers else Map()
            QB((s5, ts1, ts2, tTriggers, (auxGlobalQuants, auxNonGlobalQuants), additionalPossibleTriggers))})})})
    }){case (s2, ts1, ts2, tTriggers, (tAuxGlobal, tAux), additionalPossibleTriggers) =>
      val s3 = s.copy(possibleTriggers = s.possibleTriggers ++ additionalPossibleTriggers)
                .preserveAfterLocalEvaluation(s2)
      Q(s3, tVars, ts1, ts2, tTriggers, (tAuxGlobal, tAux), v)
    }
  }

  private def evalImplies(s: State,
                          tLhs: Term,
                          eRhs: ast.Exp,
                          fromShortCircuitingAnd: Boolean,
                          pve: PartialVerificationError,
                          v: Verifier)
                         (Q: (State, Term, Verifier) => VerificationResult)
                         : VerificationResult = {

    joiner.join[Term, Term](s, v)((s1, v1, QB) =>
      // TODO GV: we don't currently support this, so the branching information
      // passed in the second and third arguments is not correct!
      brancher.branch(s1, tLhs, ast.NullLit()(), None, v1, fromShortCircuitingAnd)(
        (s2, v2) => eval(s2, eRhs, pve, v2)(QB),
        (s2, v2) => QB(s2, True(), v2))
    )(entries => {
      assert(entries.length <= 2)
      val s1 = entries.tail.foldLeft(entries.head.s)((sAcc, entry) => sAcc.merge(entry.s))
      val t = Implies(tLhs, entries.headOption.map(_.data).getOrElse(True()))
      (s1, t)
    })(Q)
  }

  private def evalInOldState(s: State,
                             label: String,
                             e: ast.Exp,
                             pve: PartialVerificationError,
                             v: Verifier)
                            (Q: (State, Term, Verifier) => VerificationResult)
                            : VerificationResult = {

    val h = s.oldHeaps(label)
    val s1 = s.copy(h = h, partiallyConsumedHeap = None)
    val s2 = stateConsolidator.consolidateIfRetrying(s1, v)

    eval(s2, e, pve, v)((s3, t, v1) => {
      val s4 = s3.copy(h = s.h,
                       oldHeaps = s3.oldHeaps + (label -> s3.h),
                       partiallyConsumedHeap = s.partiallyConsumedHeap)
      Q(s4, t, v1)})
  }

  def evalLocationAccess(s: State,
                         locacc: ast.LocationAccess,
                         pve: PartialVerificationError,
                         v: Verifier)
                        (Q: (State, String, Seq[Term], Verifier) => VerificationResult)
                        : VerificationResult = {

    locacc match {
      case ast.FieldAccess(eRcvr, field) =>
        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          Q(s1, field.name, tRcvr :: Nil, v1))
      case ast.PredicateAccess(eArgs, predicateName) =>
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          Q(s1, predicateName, tArgs, v1))
    }
  }

  def evalLocationAccesspc(s: State,
                          locacc: ast.LocationAccess,
                          pve: PartialVerificationError,
                          v: Verifier,
                          generateChecks: Boolean = true)
                          (Q: (State, String, Seq[Term], Verifier) => VerificationResult)
                          : VerificationResult = {

    locacc match {
      case ast.FieldAccess(eRcvr, field) =>
        evalpc(s, eRcvr, pve, v, generateChecks)((s1, tRcvr, v1) =>
          Q(s1, field.name, tRcvr :: Nil, v1))
      case ast.PredicateAccess(eArgs, predicateName) =>
        evalspc(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          Q(s1, predicateName, tArgs, v1))
    }
  }

  def evalResourceAccess(s: State, resacc: ast.ResourceAccess, pve: PartialVerificationError, v: Verifier)
                        (Q: (State, ChunkIdentifer, Seq[Term], Verifier) => VerificationResult)
                        : VerificationResult = {
    resacc match {
      case wand : ast.MagicWand =>
        magicWandSupporter.evaluateWandArguments(s, wand, pve, v)((s1, tArgs, v1) =>
        Q(s1, MagicWandIdentifier(wand, Verifier.program), tArgs, v1))
      case ast.FieldAccess(eRcvr, field) =>
        eval(s, eRcvr, pve, v)((s1, tRcvr, v1) =>
          Q(s1, BasicChunkIdentifier(field.name), tRcvr :: Nil, v1))
      case ast.PredicateAccess(eArgs, predicateName) =>
        evals(s, eArgs, _ => pve, v)((s1, tArgs, v1) =>
          Q(s1, BasicChunkIdentifier(predicateName), tArgs, v1))
    }
  }

  private def evalBinOp[T <: Term]
                       (s: State,
                        e0: ast.Exp,
                        e1: ast.Exp,
                        termOp: (Term, Term) => T,
                        pve: PartialVerificationError,
                        v: Verifier)
                       (Q: (State, T, Verifier) => VerificationResult)
                       : VerificationResult = {

    eval(s, e0, pve, v)((s1, t0, v1) =>
      eval(s1, e1, pve, v1)((s2, t1, v2) =>
        Q(s2, termOp(t0, t1), v2)))
  }

  //PC version of evalBinOp
  private def evalBinOpPc[T <: Term]
                       (s: State,
                        e0: ast.Exp,
                        e1: ast.Exp,
                        termOp: (Term, Term) => T,
                        pve: PartialVerificationError,
                        v: Verifier,
                        generateChecks: Boolean = true)
                       (Q: (State, T, Verifier) => VerificationResult)
                       : VerificationResult = {

    evalpc(s, e0, pve, v, generateChecks)((s1, t0, v1) =>
      evalpc(s1, e1, pve, v1, generateChecks)((s2, t1, v2) =>
        Q(s2, termOp(t0, t1), v2)))
  }

  private def failIfDivByZero(s: State,
                              t: Term,
                              eDivisor: ast.Exp,
                              tDivisor: Term,
                              tZero: Term,
                              pve: PartialVerificationError,
                              v: Verifier)
                             (Q: (State, Term, Verifier) => VerificationResult)
                             : VerificationResult = {

    v.decider.assertgv(s.isImprecise, tDivisor !== tZero) {
      case true => Q(s, t, v)
      case false => createFailure(pve dueTo DivisionByZero(eDivisor), v, s)
    } match {
      case (verificationResult, _) => verificationResult
    }
  }

  def evalTriggers(s: State,
                   silverTriggers: Seq[ast.Trigger],
                   pve: PartialVerificationError,
                   v: Verifier)
                  (Q: (State, Seq[Trigger], Verifier) => VerificationResult)
                   : VerificationResult = {

    evalTriggers(s, silverTriggers map (_.exps), Nil, pve, v)((s1, tTriggersSets, v1) => {
      /* [2015-12-15 Malte]
       *   Evaluating triggers that did not occur in the body (and whose corresponding term has
       *   therefore not already been recorded in the context) might introduce new path conditions,
       *   in particular, new constants/functions and their definitions.
       *   This is, for example, the case in issue_0147.sil: the trigger generator can potentially
       *   replace the arithmetic expression `j+1` by a fresh, quantified variable (in the trigger,
       *   not necessarily in the quantifier body). Since it is part of the receiver of a quantified
       *   field dereference, the trigger mentioning the fresh variable might only be evaluated when
       *   evaluating the triggers, potentially leading to a newly introduced field value function.
       *
       *   TODO: Currently, new path conditions introduced while evaluating triggers will not be
       *         added to the auxiliary quantifier, i.e. they will not survive when the scope in
       *         which the quantifier (resp., its body and its triggers) is evaluated.
       *         Using such effectively "undefined" symbols in triggers will most likely result in
       *         incompletenesses because the corresponding quantifiers will not be triggered.
       */

      Q(s1, tTriggersSets map Trigger, v1)})
  }

  /** Evaluates the given list of trigger sets `eTriggerSets` (expressions) and passes the result
    * plus the initial trigger sets `tTriggerSets` (terms) to the continuation `Q`.
    */
  private def evalTriggers(s: State,
                           eTriggerSets: TriggerSets[ast.Exp],
                           tTriggersSets: TriggerSets[Term],
                           pve: PartialVerificationError,
                           v: Verifier)
                          (Q: (State, TriggerSets[Term], Verifier) => VerificationResult)
                          : VerificationResult = {

    if (eTriggerSets.isEmpty)
      Q(s, tTriggersSets, v)
    else {
      if (eTriggerSets.head.collect{case fa: ast.FieldAccess => fa; case pa: PredicateAccess => pa; case wand: ast.MagicWand => wand }.nonEmpty ) {
        evalHeapTrigger(s, eTriggerSets.head, pve, v)((s1, ts, v1) =>
          evalTriggers(s1, eTriggerSets.tail, tTriggersSets :+ ts, pve, v1)(Q))
      } else {
        evalTrigger(s, eTriggerSets.head, pve, v)((s1, ts, v1) =>
          evalTriggers(s1, eTriggerSets.tail, tTriggersSets :+ ts, pve, v1)(Q))
      }}
  }

  private def evalTrigger(s: State, exps: Seq[ast.Exp], pve: PartialVerificationError, v: Verifier)
                         (Q: (State, Seq[Term], Verifier) => VerificationResult)
                         : VerificationResult = {

    val (cachedTriggerTerms, remainingTriggerExpressions) =
      exps.map {
        case ast.Old(e) => e /* TODO: What about heap-dependent functions under old in triggers? */
        case e => e
      }.map {
        case fapp: ast.FuncApp =>
          /** Heap-dependent functions that are used as tTriggerSets should be used
            * in the limited version, because it allows for more instantiations.
            * Keep this code in sync with [[viper.silicon.supporters.ExpressionTranslator.translate]]
            *
            */
          val cachedTrigger =
            s.possibleTriggers.get(fapp) map {
              case app @ App(fun: HeapDepFun, _) =>
                app.copy(applicable = functionSupporter.limitedVersion(fun))
              case app: App =>
                app
              case other =>
                sys.error(s"Expected $fapp to map to a function application, but found $other")
            }

          (cachedTrigger, if (cachedTrigger.isDefined) None else Some(fapp))

        case pt @ (_: ast.PossibleTrigger | _: ast.FieldAccess) =>
          val cachedTrigger = s.possibleTriggers.get(pt)

          (cachedTrigger, if (cachedTrigger.isDefined) None else Some(pt))

        case e => (None, Some(e))
      }.unzip match {
        case (optCachedTriggerTerms, optRemainingTriggerExpressions) =>
          (optCachedTriggerTerms.flatten, optRemainingTriggerExpressions.flatten)
      }

    /* Reasons for why a trigger wasn't recorded while evaluating the body include:
     *   - It did not occur in the body
     *   - The evaluation of the body terminated early, for example, because the
     *     LHS of an implication evaluated to false
     */

    var optRemainingTriggerTerms: Option[Seq[Term]] = None
    val preMark = v.decider.setPathConditionMark()
    var πDelta = InsertionOrderedSet.empty[Term]

    /* TODO: Evaluate as many remaining expressions as possible, i.e. don't
     *       stop if evaluating one fails
     *
     *       Here is an example where evaluating remainingTriggerExpressions will
     *       fail: Assume a conjunction f(x) && g(x) where f(x) is the
     *       precondition of g(x). This gives rise to the trigger {f(x), g(x)}.
     *       If the two trigger expressions are evaluated individually, evaluating
     *       the second will fail because its precondition doesn't hold.
     *       For example, let f(x) be "x in xs" (and assume that this, via other
     *       path conditions, implies that x != null), and let g(x) be "y.f in xs".
     *       Evaluating the latter will currently fail when evaluating y.f because
     *       y on its own (i.e., without having assumed y in xs) might be null.
     *
     *       What might be possible is to merely translate (instead of evaluate)
     *       triggers, where the difference is that translating does not entail
     *       any checks such as checking for non-nullity.
     *       In case of applications of heap. dep. functions this won't be
     *       straight-forward, because the resulting FApp-term expects a snapshot,
     *       which is computed by (temporarily) consuming the function's
     *       precondition.
     *       We could replace each concrete snapshot occurring in an FApp-term by
     *       a quantified snapshot, but that might make the chosen triggers invalid
     *       because some trigger sets might no longer cover all quantified
     *       variables.
     */

    /* TODO: Use executionFlowController.locally instead of val r = ...; r && { ... }.
     *       This is currently not possible because executionFlowController.locally will only
     *       continue after the local block if the block was successful (i.e. if it yielded
     *       Success()). However, here we want to continue in any case.
     */

    val r =
      evals(s, remainingTriggerExpressions, _ => pve, v)((_, remainingTriggerTerms, v1) => {
        optRemainingTriggerTerms = Some(remainingTriggerTerms)
        πDelta = v1.decider.pcs.after(preMark).assumptions //decider.π -- πPre
        Success()})

    (r, optRemainingTriggerTerms) match {
      case (Success(), Some(remainingTriggerTerms)) =>
        v.decider.assume(πDelta)
        Q(s, cachedTriggerTerms ++ remainingTriggerTerms, v)
      case _ =>
//        bookkeeper.logfiles("evalTrigger").println(s"Couldn't evaluate some trigger expressions:\n  $remainingTriggerExpressions\nReason:\n  $r")
        Q(s, cachedTriggerTerms, v)
    }
  }

  private def join(joinSort: Sort,
                   joinFunctionName: String,
                   joinFunctionArgs: Seq[Term],
                   v: Verifier)
                  (entries: Seq[JoinDataEntry[Term]])
                  : (State, Term) = {

    assert(entries.nonEmpty, "Expected at least one join data entry")

    entries match {
      case Seq(entry) =>
        /* If there is only one entry, i.e. one branch to join, it is assumed that the other
         * branch was infeasible, and the branch conditions are therefore ignored.
         */
        (entry.s, entry.data)
      case _ =>
        val quantifiedVarsSorts = joinFunctionArgs.map(_.sort)
        val joinSymbol = v.decider.fresh(joinFunctionName, quantifiedVarsSorts, joinSort)
        val joinTerm = App(joinSymbol, joinFunctionArgs)

        val joinDefEqs = entries map (entry =>
          Implies(And(entry.pathConditions.branchConditions), joinTerm === entry.data))

        var sJoined = entries.tail.foldLeft(entries.head.s)((sAcc, entry) =>sAcc.merge(entry.s))
        sJoined = sJoined.copy(functionRecorder = sJoined.functionRecorder.recordPathSymbol(joinSymbol))

        v.decider.assume(joinDefEqs)

        (sJoined, joinTerm)
    }
  }

  private def evalHeapTrigger(s: State, exps: Seq[ast.Exp], pve: PartialVerificationError, v: Verifier)
                             (Q: (State, Seq[Term], Verifier) => VerificationResult) : VerificationResult = {
    var triggers: Seq[Term] = Seq()
    var triggerAxioms: Seq[Term] = Seq()

    exps foreach {
      case fa: ast.FieldAccess =>
        val (axioms, trigs, _) = generateFieldTrigger(fa, s, pve, v)
        triggers = triggers ++ trigs
        triggerAxioms = triggerAxioms ++ axioms
      case pa: ast.PredicateAccess =>
        val (axioms, trigs, _) = generatePredicateTrigger(pa, s, pve, v)
        triggers = triggers ++ trigs
        triggerAxioms = triggerAxioms ++ axioms
      case wand: ast.MagicWand =>
        val (axioms, trigs, _) = generateWandTrigger(wand, s, pve, v)
        triggers = triggers ++ trigs
        triggerAxioms = triggerAxioms ++ axioms
      case e => evalTrigger(s, Seq(e), pve, v)((_, t, _) => {
        triggers = triggers ++ t
        Success()
      })
    }
    v.decider.assume(triggerAxioms)
    Q(s, triggers, v)
  }

  private def generateFieldTrigger(fa: ast.FieldAccess,
                                   s: State,
                                   pve: PartialVerificationError,
                                   v: Verifier)
                                  : (Seq[Term], Seq[Term], FieldTrigger) = {

    var axioms = Seq.empty[Term]
    var triggers = Seq.empty[Term]
    var mostRecentTrig: FieldTrigger = null
    val codomainQVars = Seq(`?r`)
    val (relevantChunks, _) =
      quantifiedChunkSupporter.splitHeap[QuantifiedFieldChunk](s.h, BasicChunkIdentifier(fa.field.name))
    val optSmDomainDefinitionCondition =
      if (s.smDomainNeeded) { v.logger.debug("Axiomatisation of an SM domain missing!"); None }
      else None
    val (smDef1, smCache1) =
      quantifiedChunkSupporter.summarisingSnapshotMap(
        s, fa.field, codomainQVars, relevantChunks, v, optSmDomainDefinitionCondition)

    /* TODO: Reduce code duplication below */
    /* TODO: Return updated snapshot caches (or let generateFieldTrigger take a continuation) */

    fa.rcv match {
      case acc: ast.FieldAccess =>
        /* TODO: Is this *recursive* case even necessary? Wouldn't the eval(...) in the other case
         *       recurse anyway?
         */
        val rcvHelper = generateFieldTrigger(acc, s, pve, v)
        val rcvTrig = rcvHelper._3
        axioms = axioms ++ smDef1.valueDefinitions ++ rcvHelper._1
        mostRecentTrig = FieldTrigger(fa.field.name, smDef1.sm, Lookup(rcvTrig.field, rcvTrig.fvf, rcvTrig.at))
        triggers = triggers ++ rcvHelper._2 :+ mostRecentTrig
      case rcv =>
        val s1 = s.copy(smCache = smCache1)
        val t = s1.possibleTriggers.get(fa)
        val r = t match { /* TODO: r isn't used - why? */
          case Some(cachedTrigger) =>
            cachedTrigger match {
              case l: Lookup =>
                axioms = axioms ++ smDef1.valueDefinitions
                mostRecentTrig = FieldTrigger(l.field, smDef1.sm, l.at)
                triggers = triggers :+ mostRecentTrig
              case _ =>
                eval(s1.copy(triggerExp = true), rcv, pve, v)((_, tRcv, _) => {
                  axioms = axioms ++ smDef1.valueDefinitions
                  mostRecentTrig = FieldTrigger(fa.field.name, smDef1.sm, tRcv)
                  triggers = triggers :+ mostRecentTrig
                  Success()
                })
            }
          case None =>
            eval(s1.copy(triggerExp = true), rcv, pve, v)((_, tRcv, _) => {
              axioms = axioms ++ smDef1.valueDefinitions
              mostRecentTrig = FieldTrigger(fa.field.name, smDef1.sm, tRcv)
              triggers = triggers :+ mostRecentTrig
              Success()
            })
        }
    }

    (axioms, triggers, mostRecentTrig)
  }

  /* TODO: Try to unify with generateFieldTrigger above, or at least with generateWandTrigger below */
  private def generatePredicateTrigger(pa: ast.PredicateAccess, s: State, pve: PartialVerificationError, v: Verifier): (Seq[Term], Seq[Term], PredicateTrigger) = {
    var axioms = Seq.empty[Term]
    var triggers = Seq.empty[Term]
    var mostRecentTrig: PredicateTrigger = null
    val codomainQVars = s.predicateFormalVarMap(pa.loc(Verifier.program))
    val (relevantChunks, _) =
      quantifiedChunkSupporter.splitHeap[QuantifiedPredicateChunk](s.h, BasicChunkIdentifier(pa.predicateName))
    val optSmDomainDefinitionCondition =
      if (s.smDomainNeeded) { v.logger.debug("Axiomatisation of an SM domain missing!"); None }
      else None
    val (smDef1, smCache1) =
      quantifiedChunkSupporter.summarisingSnapshotMap(
        s, pa.loc(Verifier.program), codomainQVars, relevantChunks, v, optSmDomainDefinitionCondition)
    val s1 = s.copy(smCache = smCache1)

    evals(s1, pa.args, _ => pve, v)((_, tArgs, _) => {
      axioms = axioms ++ smDef1.valueDefinitions
      mostRecentTrig = PredicateTrigger(pa.predicateName, smDef1.sm, tArgs)
      triggers = triggers :+ mostRecentTrig
      Success()
    })

    (axioms, triggers, mostRecentTrig)
  }

  /* TODO: See comments for generatePredicateTrigger above */
  private def generateWandTrigger(wand: ast.MagicWand, s: State, pve: PartialVerificationError, v: Verifier): (Seq[Term], Seq[Term], PredicateTrigger) = {
    var axioms = Seq.empty[Term]
    var triggers = Seq.empty[Term]
    var mostRecentTrig: PredicateTrigger = null
    val wandHoles = wand.subexpressionsToEvaluate(Verifier.program)
    val codomainQVars =
      wandHoles.indices.toList.map(i => Var(Identifier(s"x$i"), v.symbolConverter.toSort(wandHoles(i).typ)))
    val (relevantChunks, _) =
      quantifiedChunkSupporter.splitHeap[QuantifiedMagicWandChunk](s.h, MagicWandIdentifier(wand, Verifier.program))
    val optSmDomainDefinitionCondition =
      if (s.smDomainNeeded) { v.logger.debug("Axiomatisation of an SM domain missing!"); None }
      else None
    val (smDef1, smCache1) =
      quantifiedChunkSupporter.summarisingSnapshotMap(
        s, wand, codomainQVars, relevantChunks, v, optSmDomainDefinitionCondition)
    val s1 = s.copy(smCache = smCache1)

    evals(s1, wand.subexpressionsToEvaluate(Verifier.program), _ => pve, v)((_, tArgs, _) => {
      axioms = axioms ++ smDef1.valueDefinitions
      mostRecentTrig = PredicateTrigger(MagicWandIdentifier(wand, Verifier.program).toString, smDef1.sm, tArgs)
      triggers = triggers :+ mostRecentTrig
      Success()
    })

    (axioms, triggers, mostRecentTrig)
  }

  /* Evaluate a sequence of expressions in Order
   * The constructor determines when the evaluation stops
   * Only Or and And are supported for the constructor
   */
  private def evalSeqShortCircuit(constructor: Seq[Term] => Term,
                                  s: State,
                                  exps: Seq[ast.Exp],
                                  pve: PartialVerificationError,
                                  v: Verifier)
                                 (Q: (State, Term, Verifier) => VerificationResult)
                                 : VerificationResult = {
    assert(
      constructor == Or || constructor == And,
      "Only Or and And are supported as constructors for evalSeqShortCircuit")

    assert(exps.nonEmpty, "Empty sequence of expressions not allowed")

    type brFun = (State, Verifier) => VerificationResult

    val stop = if (constructor == Or) True() else False()

    eval(s, exps.head, pve, v)((s1, t0, v1) => {
      t0 match {
        case _ if exps.tail.isEmpty => Q(s1, t0, v1) // Done, if no expressions left (necessary)
        case `stop` => Q(s1, t0, v1) // Done, if last expression was true/false for or/and (optimisation)
        case _ => {
          // Get branch origin for brancher.branch
            val branchCondOrigin: Option[CheckPosition] =
              (s1.methodCallAstNode, s1.foldOrUnfoldAstNode, s1.loopPosition, s1.unfoldingAstNode) match {
                case (None, None, None, None) => None
                case (Some(methodCallAstNode), None, None, _) =>
                  Some(CheckPosition.GenericNode(methodCallAstNode))
                case (None, Some(foldOrUnfoldAstNode), None, _) =>
                  Some(CheckPosition.GenericNode(foldOrUnfoldAstNode))
                case (None, None, Some(loopPosition), _) =>
                  Some(loopPosition)
                case (None, None, None, Some(unfoldingAstNode)) =>
                  Some(CheckPosition.GenericNode(unfoldingAstNode))
                case _ =>
                  println((s1.methodCallAstNode, s1.foldOrUnfoldAstNode, s1.loopPosition, s1.unfoldingAstNode))
                  sys.error("Error: _ match case when setting a branch condition origin!")
              }

          joiner.join[Term, Term](s1, v1)((s2, v2, QB) =>            
            brancher.branch(s2, if (constructor == Or) t0 else Not(t0), exps.head, branchCondOrigin, v2, true)(
              (s3, v3) => QB(s3, constructor(Seq(t0)), v3),
              (s3, v3) => evalSeqShortCircuit(constructor, s3, exps.tail, pve, v3)(QB))
            ){case Seq(ent) =>
                (ent.s, ent.data)
              case Seq(ent1, ent2) =>
                (ent1.s.merge(ent2.s), constructor(Seq(ent1.data, ent2.data)))
              case entries =>
                sys.error(s"Unexpected join data entries $entries")
            }(Q)
        }
      }})
  }

    /* Evaluate a sequence of expressions in Order
   * The constructor determines when the evaluation stops
   * Only Or and And are supported for the constructor
   */
  private def evalSeqShortCircuitPc(constructor: Seq[Term] => Term,
                                  s: State,
                                  exps: Seq[ast.Exp],
                                  pve: PartialVerificationError,
                                  v: Verifier,
                                  generateChecks: Boolean = true)
                                 (Q: (State, Term, Verifier) => VerificationResult)
                                 : VerificationResult = {
    assert(
      constructor == Or || constructor == And,
      "Only Or and And are supported as constructors for evalSeqShortCircuitPc")

    assert(exps.nonEmpty, "Empty sequence of expressions not allowed")

    type brFun = (State, Verifier) => VerificationResult

    // // // TODO: Find out and document why swapIfAnd is needed
    // val (stop, swapIfAnd) =
    //   if(constructor == Or) (True(), (a: brFun, b: brFun) => (a, b))
    //   else (False(), (a: brFun, b: brFun) => (a, b))
    val stop = if (constructor == Or) True() else False()

    evalpc(s, exps.head, pve, v, generateChecks)((s1, t0, v1) => {
      t0 match {
        case _ if exps.tail.isEmpty => Q(s1, t0, v1) // Done, if no expressions left (necessary)
        case `stop` => Q(s1, t0, v1) // Done, if last expression was true/false for or/and (optimisation)
        case _ => {
          // Get branch origin for brancher.branch
            val branchCondOrigin: Option[CheckPosition] =
              (s1.methodCallAstNode, s1.foldOrUnfoldAstNode, s1.loopPosition, s1.unfoldingAstNode) match {
                case (None, None, None, _) => None
                case (Some(methodCallAstNode), None, None, None) =>
                  Some(CheckPosition.GenericNode(methodCallAstNode))
                case (None, Some(foldOrUnfoldAstNode), None, _) =>
                  Some(CheckPosition.GenericNode(foldOrUnfoldAstNode))
                case (None, None, Some(loopPosition), _) =>
                  Some(loopPosition)
                case (None, None, None, Some(unfoldingAstNode)) =>
                  Some(CheckPosition.GenericNode(unfoldingAstNode))
                case _ =>
                  println((s1.methodCallAstNode, s1.foldOrUnfoldAstNode, s1.loopPosition, s1.unfoldingAstNode))
                  sys.error("Error: _ match case when setting a branch condition origin!")
              }

          joiner.join[Term, Term](s1, v1)((s2, v2, QB) =>            
            brancher.branch(s2, if (constructor == Or) t0 else Not(t0), exps.head, branchCondOrigin, v2, true)(
              (s3, v3) => QB(s3, constructor(Seq(t0)), v3),
              (s3, v3) => evalSeqShortCircuitPc(constructor, s3, exps.tail, pve, v3, generateChecks)(QB))
            ){case Seq(ent) =>
                (ent.s, ent.data)
              case Seq(ent1, ent2) =>
                (ent1.s.merge(ent2.s), constructor(Seq(ent1.data, ent2.data)))
              case entries =>
                sys.error(s"Unexpected join data entries $entries")
            }(Q)
        }
      }})
  }

  private[silicon] case object FromShortCircuitingAnd extends Info {
    val comment = Nil
    val isCached = false
  }
}
