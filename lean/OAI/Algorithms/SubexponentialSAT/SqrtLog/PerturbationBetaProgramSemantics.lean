import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgramRun

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing

/-- The concrete arithmetic result of one selected row is its actual node
value plus the preceding accumulator. -/
theorem nextValue_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (P : List (Coeff t d))
    (theta acc : Coeff t d) :
    (RingProgram.modelRing t ht hd a M cache).decode (nextValue t a M cache P theta acc) =
      (PerturbationProgram.polynomial (RingProgram.modelRing t ht hd a M cache) P).eval
        ((RingProgram.modelRing t ht hd a M cache).decode theta) +
          (RingProgram.modelRing t ht hd a M cache).decode acc := by
  let ops := RingProgram.modelRing t ht hd a M cache
  change ops.decode (ops.addRun (HornerProgram.modelValue t a M cache P theta) acc).1 = _
  rw [ops.add_correct,HornerProgram.modelValue_decode t ht hd a M cache P theta]
  rfl

theorem fold_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (theta acc : Coeff t d)
    (rows : List (List (Coeff t d) × Bool)) :
    (RingProgram.modelRing t ht hd a M cache).decode
      (rows.foldl (stepValue t a M cache theta) acc) =
      (RingProgram.modelRing t ht hd a M cache).decode acc +
        PerturbationProgram.betaValue (RingProgram.modelRing t ht hd a M cache) theta rows := by
  induction rows generalizing acc with
  | nil => simp [PerturbationProgram.betaValue]
  | cons row rows ih =>
    rcases row with ⟨P,b⟩
    rw [List.foldl_cons,ih]
    cases b
    · simp [stepValue,PerturbationProgram.betaValue]
    · simp only [stepValue,ite_true]
      rw [nextValue_decode t ht hd a M cache P theta acc]
      simp only [PerturbationProgram.betaValue,List.map_cons,List.sum_cons,ite_true]
      ring

theorem runValue_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (theta : Coeff t d)
    (rows : List (List (Coeff t d) × Bool)) :
    (RingProgram.modelRing t ht hd a M cache).decode (runValue t a M cache theta rows) =
      PerturbationProgram.betaValue (RingProgram.modelRing t ht hd a M cache) theta rows := by
  rw [runValue,fold_decode t ht hd a M cache]
  have hz := (RingProgram.modelRing t ht hd a M cache).zero_correct
  rw [← RingProgram.modelRing_program t ht hd a M cache]
  simpa using congrArg (fun x => x + PerturbationProgram.betaValue
    (RingProgram.modelRing t ht hd a M cache) theta rows) hz

/-- Compilation of the fixed concrete command, with the exact decoded beta
and complete framing. No evaluated-row service is an input. -/
theorem betaMachine_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta : Coeff t d) (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
    (hL : ∀ row∈rows,row.1.length=L)
    (h205 : base 205=rowsBits rows) (h206 : base 206=rows.map Prod.snd)
    (h207 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (h209 : base 209=RingProgram.flat theta)
    (h210 : (base 210).length=L) (h211 : (base 211).length=d*baseWidth 3 t)
    (he : WorkEmpty base) (regs : Fin 16 → Bool) :
    ∃ out rf, RunsIn betaMachine (runBudget base rows.length L t d+1)
      ((⟨regs,base⟩ : Data).withPC (some betaMachine.entry))
      ((⟨rf,Function.update base 220 (RingProgram.flat out)⟩ : Data).withPC none) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        PerturbationProgram.betaValue (RingProgram.modelRing t ht hd a M cache) theta rows := by
  obtain ⟨n,rf,hn,hrun⟩ := betaCommand_run t a M cache hz base hready theta rows L hL
    h205 h206 h207 h209 h210 h211 he regs
  refine ⟨runValue t a M cache theta rows,rf,?_,runValue_decode t ht hd a M cache theta rows⟩
  exact ⟨n+1,by omega,compiled_halt_trace hrun 205 220⟩

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
