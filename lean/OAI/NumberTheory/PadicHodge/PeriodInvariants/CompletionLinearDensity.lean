import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Completion Linear Density -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CompletionLinearDensity

/-! # Linear maps out of completions are determined by the original module -/

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (I : Ideal R) (hI : I.FG) [IsHausdorff I N]

include hI in
theorem ext (f g : AdicCompletion I M →ₗ[R] N)
    (h : ∀ x, f (AdicCompletion.of I M x) = g (AdicCompletion.of I M x)) : f = g := by
  apply LinearMap.ext
  intro x
  apply sub_eq_zero.mp
  apply IsHausdorff.haus' (I := I)
  intro n
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule R M)) (AdicCompletion.eval I M n x)
  have hx : x - AdicCompletion.of I M a ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub]
    change AdicCompletion.eval I M n x - Submodule.Quotient.mk a = 0
    exact sub_eq_zero.mpr ha.symm
  have hm : Submodule.map (f - g) (I ^ n • (⊤ : Submodule R (AdicCompletion I M))) ≤
      I ^ n • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top
  have hh := hm (show (f - g) (x - AdicCompletion.of I M a) ∈
      Submodule.map (f - g) (I ^ n • (⊤ : Submodule R (AdicCompletion I M))) from ⟨_, hx, rfl⟩)
  simp only [map_sub, LinearMap.sub_apply, h a, sub_self, sub_zero] at hh
  simpa only [SModEq.sub_mem, sub_zero] using hh

include hI in
theorem double_ext (J : Ideal R) (hJ : J.FG) [IsHausdorff J N]
    (f g : AdicCompletion J (AdicCompletion I M) →ₗ[R] N)
    (h : ∀ x, f (AdicCompletion.of J _ (AdicCompletion.of I M x)) =
      g (AdicCompletion.of J _ (AdicCompletion.of I M x))) : f = g := by
  apply CompletionLinearDensity.ext J hJ
  have he : f.comp (AdicCompletion.of J (AdicCompletion I M)) =
      g.comp (AdicCompletion.of J (AdicCompletion I M)) := CompletionLinearDensity.ext I hI _ _ h
  exact LinearMap.congr_fun he

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CompletionLinearDensity
