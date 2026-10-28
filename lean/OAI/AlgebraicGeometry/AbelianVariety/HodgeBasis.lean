import OAI.AlgebraicGeometry.AbelianVariety.CupGeneration
import OAI.AlgebraicGeometry.AbelianVariety.PureAverage
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Hodge Basis -/

namespace OAI.AlgebraicGeometry.AbelianVariety.HodgeBasis.Constructions.ExteriorCohomology

noncomputable section

open scoped TensorProduct Classical

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

abbrev HodgeBasisIndex (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) :=
  Fin (Module.finrank ℂ H.holomorphic) ⊕ Fin (Module.finrank ℂ H.antiholomorphic)

def hodgeBasis (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) :
    Module.Basis (HodgeBasisIndex H) ℂ (ComplexMultiplication.WeightOne.CM.Complexification U) := by
  let : FiniteDimensional ℚ U := H.finiteDimensional
  exact ((Module.finBasis ℂ H.holomorphic).prod
    (Module.finBasis ℂ H.antiholomorphic)).map
      (Submodule.prodEquivOfIsCompl _ _ H.complementary)

def hodgeBasisSign (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) : HodgeBasisIndex H → Bool
  | .inl _ => true
  | .inr _ => false

theorem hodgeBasis_mem_signSubspace (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (i : HodgeBasisIndex H) :
    hodgeBasis H i ∈ H.signSubspace (hodgeBasisSign H i) := by
  let : FiniteDimensional ℚ U := H.finiteDimensional
  cases i with
  | inl i =>
    change hodgeBasis H (.inl i) ∈ H.holomorphic
    have he : hodgeBasis H (.inl i) = (Module.finBasis ℂ H.holomorphic i).val := by
      simp [hodgeBasis, Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
    rw [he]
    exact (Module.finBasis ℂ H.holomorphic i).property
  | inr i =>
    change hodgeBasis H (.inr i) ∈ H.antiholomorphic
    have he : hodgeBasis H (.inr i) = (Module.finBasis ℂ H.antiholomorphic i).val := by
      simp [hodgeBasis, Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
    rw [he]
    exact (Module.finBasis ℂ H.antiholomorphic i).property

theorem signSubspace_eq_span_hodgeBasis (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (b : Bool) :
    H.signSubspace b = Submodule.span ℂ ((hodgeBasis H) '' {i | hodgeBasisSign H i = b}) := by
  apply le_antisymm
  · intro x hx
    let P := (H.signSubspace b).projection (H.signSubspace (!b)) (H.signSubspace_isCompl b)
    have hp : P x = x := Submodule.projection_apply_of_mem_left (H.signSubspace_isCompl b) hx
    have he := congrArg P ((hodgeBasis H).sum_repr x)
    rw [hp] at he
    rw [← he]
    simp only [map_sum, map_smul]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : hodgeBasisSign H j = b
    · have hm : hodgeBasis H j ∈ H.signSubspace b := hj ▸ hodgeBasis_mem_signSubspace H j
      rw [Submodule.projection_apply_of_mem_left (H.signSubspace_isCompl b) hm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · have hj' : hodgeBasisSign H j = !b := by
        cases b <;> cases heq : hodgeBasisSign H j <;> simp_all
      have hm : hodgeBasis H j ∈ H.signSubspace (!b) := hj' ▸ hodgeBasis_mem_signSubspace H j
      rw [Submodule.projection_apply_of_mem_right (H.signSubspace_isCompl b) hm, smul_zero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    exact hj ▸ hodgeBasis_mem_signSubspace H j

local instance (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) : LinearOrder (HodgeBasisIndex H) :=
  linearOrderOfSTO WellOrderingRel

def hodgeExteriorBasis (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (n : ℕ) :
    Module.Basis (Set.powersetCard (HodgeBasisIndex H) n) ℂ
      (ComplexMultiplication.WeightOne.CM.Complexification (⋀[ℚ]^n U)) :=
  ((hodgeBasis H).exteriorPower n).map (ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ U n).symm

theorem exteriorSignedSubspace_eq_hodgeBasisSpan (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)
    (n : ℕ) (w : ℤ) :
    H.exteriorSignedSubspace n w = Submodule.span ℂ
      ((hodgeExteriorBasis H n) '' {t | ComplexMultiplication.ExteriorTypedBasis.CM.exteriorBasisSignSum n (hodgeBasisSign H) t = w}) := by
  unfold ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.exteriorSignedSubspace
  rw [ComplexMultiplication.ExteriorTypedBasis.CM.exteriorSignedSpan_eq_basisSpan n (hodgeBasis H) (hodgeBasisSign H) w H.signSubspace
    (signSubspace_eq_span_hodgeBasis H)]
  unfold ComplexMultiplication.ExteriorTypedBasis.CM.exteriorSignedBasisSpan
  rw [Submodule.map_span, Set.image_image]
  rfl

end

end OAI.AlgebraicGeometry.AbelianVariety.HodgeBasis.Constructions.ExteriorCohomology
