import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionExtension
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Rational Completion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The supplied split integral completion determines the actual split
rational completion, with the same integral local characters. -/

open scoped TensorProduct Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)

def Data.SphericalPELAlbaneseData.rationalLocalCharacter (v : Fin s × Bool) : E →ₐ[ℚ] ℚ_[q] :=
  AbelianModuli.ReferenceFamily.Integral.ActionExtension.extendIntegralAction ((algebraMap ℤ_[q] ℚ_[q]).comp (D.localCharacter v))

theorem Data.SphericalPELAlbaneseData.rationalLocalCharacter_integer (v : Fin s × Bool) (a : NumberField.RingOfIntegers E) :
    D.rationalLocalCharacter v (a : E) = algebraMap ℤ_[q] ℚ_[q] (D.localCharacter v a) :=
  AbelianModuli.ReferenceFamily.Integral.ActionExtension.extendIntegralAction_integer _ a

def Data.SphericalPELAlbaneseData.rationalCompletionMap : ℚ_[q] ⊗[ℚ] E →ₐ[ℚ_[q]] (Fin s × Bool → ℚ_[q]) :=
  AlgHom.liftEquiv ℚ ℚ_[q] E _ (AlgHom.pi D.rationalLocalCharacter)

theorem Data.SphericalPELAlbaneseData.rationalCompletionMap_tmul (z : ℚ_[q]) (a : E) (v : Fin s × Bool) :
    D.rationalCompletionMap (z ⊗ₜ[ℚ] a) v = z * D.rationalLocalCharacter v a := rfl

theorem Data.SphericalPELAlbaneseData.localCompletionMap_tmul (z : ℤ_[q]) (a : NumberField.RingOfIntegers E) (v : Fin s × Bool) :
    D.localCompletionMap (z ⊗ₜ[ℤ] a) v = z * D.localCharacter v a := rfl

theorem Data.SphericalPELAlbaneseData.rationalCompletion_range_contains_integral
    (t : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) :
    (fun v => algebraMap ℤ_[q] ℚ_[q] (D.localCompletionMap t v)) ∈
      D.rationalCompletionMap.toLinearMap.range := by
  induction t using TensorProduct.inductionOn with
  | tmul z a =>
    refine ⟨algebraMap ℤ_[q] ℚ_[q] z ⊗ₜ[ℚ] (a : E), ?_⟩
    funext v
    rw [AlgHom.toLinearMap_apply, Data.SphericalPELAlbaneseData.rationalCompletionMap_tmul, Data.SphericalPELAlbaneseData.rationalLocalCharacter_integer,
      Data.SphericalPELAlbaneseData.localCompletionMap_tmul, map_mul]
  | add t u ht hu =>
    simpa only [map_add, Pi.add_apply, Pi.add_def] using D.rationalCompletionMap.toLinearMap.range.add_mem ht hu

theorem Data.SphericalPELAlbaneseData.rationalCompletionMap_surjective (h : D.IsGoodCompletelySplitPrime) :
    Function.Surjective D.rationalCompletionMap := by
  have hb (v : Fin s × Bool) : Pi.single v (1 : ℚ_[q]) ∈ D.rationalCompletionMap.toLinearMap.range := by
    obtain ⟨t, ht⟩ := h.1.2 (Pi.single v 1)
    have hm := D.rationalCompletion_range_contains_integral t
    rw [ht] at hm
    have he : (fun w => algebraMap ℤ_[q] ℚ_[q] ((Pi.single v 1 : Fin s × Bool → ℤ_[q]) w)) =
        (Pi.single v 1 : Fin s × Bool → ℚ_[q]) := by
      funext w
      by_cases hw : w = v <;> simp [hw]
    exact he ▸ hm
  apply LinearMap.range_eq_top.mp
  apply le_antisymm le_top
  rw [← (Pi.basisFun ℚ_[q] (Fin s × Bool)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, rfl⟩
  change (Pi.basisFun ℚ_[q] (Fin s × Bool)) v ∈ D.rationalCompletionMap.toLinearMap.range
  simpa only [Pi.basisFun_apply] using hb v

theorem Data.SphericalPELAlbaneseData.rationalCompletionMap_bijective (h : D.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) : Function.Bijective D.rationalCompletionMap := by
  let basis := (NumberField.integralBasis E).baseChange ℚ_[q]
  have : Module.Finite ℚ_[q] (ℚ_[q] ⊗[ℚ] E) := Module.Finite.of_basis basis
  have hr : Module.finrank ℚ_[q] (ℚ_[q] ⊗[ℚ] E) =
      Module.finrank ℚ_[q] (Fin s × Bool → ℚ_[q]) := by
    rw [Module.finrank_eq_card_basis basis]
    have hd := Module.finrank_eq_card_basis (NumberField.integralBasis E)
    rw [← hd, hdegree]
    simp [Nat.mul_comm]
  have hs := D.rationalCompletionMap_surjective h
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mpr hs, hs⟩

def Data.SphericalPELAlbaneseData.rationalCompletionEquiv (h : D.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) :
    ℚ_[q] ⊗[ℚ] E ≃ₐ[ℚ_[q]] (Fin s × Bool → ℚ_[q]) :=
  AlgEquiv.ofBijective D.rationalCompletionMap (D.rationalCompletionMap_bijective h hdegree)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
