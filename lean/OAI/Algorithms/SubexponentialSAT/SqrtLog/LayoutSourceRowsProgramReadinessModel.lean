import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramModel

namespace OAI.Algorithms

/-! Concrete ternary-model specialization of source-executor readiness. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LayoutSourceRowsProgram

theorem model_initialized_ready (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : LayoutSourceRowsProgram.Store) (D : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 t M cache
      (HornerProgram.modelTable t a M cache) (s ∘ executorPorts) width frame)
    (E : Empty s) :
    PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
      (executionContext (evaluationInput (initializeFinish s D (d*baseWidth 3 t)))) := by
  exact initialized_ready 3 t M cache (HornerProgram.modelTable t a M cache)
    (RingProgram.modelProgram t a M cache)
    (DensePolynomialProgram.model_zero_bits t a M cache hz) s D width frame H E

theorem model_ready_of_low_agreement (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s after : LayoutSourceRowsProgram.Store) (D : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 t M cache
      (HornerProgram.modelTable t a M cache) (s ∘ executorPorts) width frame)
    (E : Empty s)
    (hf : ∀ i : Fin 340, i.val < 256 → after i = initializeFinish s D (d*baseWidth 3 t) i) :
    PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
      (executionContext (evaluationInput after)) := by
  rw [executionContext_evaluation_congr after (initializeFinish s D (d*baseWidth 3 t)) hf]
  exact model_initialized_ready t a M cache hz s D width frame H E

/-- Paid initialization and the resulting concrete executor readiness share
the same full source dimension D. Existing target caches are not consulted. -/
theorem model_initialize_and_ready (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : LayoutSourceRowsProgram.Store) (D : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (H : DensePolynomialProgram.PairSpec.BaseReady 3 t M cache
      (HornerProgram.modelTable t a M cache) (s ∘ executorPorts) width frame)
    (E : Empty s)
    (HI : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D (d*baseWidth 3 t)) :
    LayoutSourceRowsProgram.ExecutesIn initializeSource
      (LayoutSourceRowsProgramInitialize.budget D (d*baseWidth 3 t)+1) s
      (initializeFinish s D (d*baseWidth 3 t)) ∧
    PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
      (executionContext (evaluationInput (initializeFinish s D (d*baseWidth 3 t)))) := by
  exact ⟨initializeSource_run s D (d*baseWidth 3 t) HI,
    model_initialized_ready t a M cache hz s D width frame H E⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness

end OAI.Algorithms
