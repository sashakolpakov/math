import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Completion Density -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.CompletionDensity.SemilinearCompletionDensity

/-! # Semilinear maps out of an adic completion are determined on the original module -/

variable {R S M N : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (σ : R →+* S) (I : Ideal R) (J : Ideal S) (hI : I.FG) (hIJ : I.map σ ≤ J)
  [IsHausdorff J N]

include hI hIJ in
theorem ext (f g : AdicCompletion I M →ₛₗ[σ] N)
    (h : ∀ a, f (AdicCompletion.of I M a) = g (AdicCompletion.of I M a)) : f = g := by
  apply LinearMap.ext
  intro x
  apply sub_eq_zero.mp
  apply IsHausdorff.haus' (I := J)
  intro n
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule R M)) (AdicCompletion.eval I M n x)
  have hx : x - AdicCompletion.of I M a ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub]
    change AdicCompletion.eval I M n x - Submodule.Quotient.mk a = 0
    exact sub_eq_zero.mpr ha.symm
  have hh : (f - g) (x - AdicCompletion.of I M a) ∈ J ^ n • (⊤ : Submodule S N) :=
    NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionSemilinear.preserves_powers σ I J hIJ n (f - g) hx
  simp only [map_sub, LinearMap.sub_apply, h a, sub_self, sub_zero] at hh
  simpa only [SModEq.sub_mem, sub_zero] using hh

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.CompletionDensity.SemilinearCompletionDensity
