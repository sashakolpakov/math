import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCoordinates
import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne

/-! # Canonical Holomorphic Coordinates -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CanonicalHolomorphicCoordinates.CM.Construction

noncomputable section

/-! The rational period coordinates identify with the holomorphic
subspace of the actual canonical rational Hodge structure. -/

open scoped TensorProduct

variable {ι : Type} [Fintype ι] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (b : Module.Basis ι ℚ (V.rationalCohomology 1))

theorem rationalCoordinates_complexification (c : ι → ℂ) :
    CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1
      ((b.baseChange ℂ).equivFun.symm c) = (RationalCoordinates.CM.Construction.rationalH1ComplexBasis V b).equivFun.symm c := by
  classical
  rw [Module.Basis.equivFun_symm_apply, map_sum, Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, Module.Basis.baseChange_apply, CohomologyBaseChange.CM.singularCohomologyComplexification_tmul,
    one_smul, RationalCoordinates.CM.Construction.rationalH1ComplexBasis_apply]
  rfl

variable (H : WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1))
  (hH : H.holomorphic = (V.pureBettiSubspace 1 0).comap
    (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1))

def canonicalHolomorphicCoordinateEquiv :
    RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b ≃ₗ[ℂ] H.holomorphic where
  toFun c := ⟨(b.baseChange ℂ).equivFun.symm c, by
    rw [hH]
    change CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1
      ((b.baseChange ℂ).equivFun.symm c) ∈ V.pureBettiSubspace 1 0
    rw [rationalCoordinates_complexification]
    exact c.property⟩
  invFun u := ⟨(b.baseChange ℂ).equivFun u, by
    change (RationalCoordinates.CM.Construction.rationalH1ComplexBasis V b).equivFun.symm ((b.baseChange ℂ).equivFun u) ∈
      V.pureBettiSubspace 1 0
    rw [← rationalCoordinates_complexification, LinearEquiv.symm_apply_apply]
    exact (congrArg (fun S : Submodule ℂ (WeightOne.CM.Complexification (V.rationalCohomology 1)) =>
      (u : WeightOne.CM.Complexification (V.rationalCohomology 1)) ∈ S) hH).mp u.property⟩
  left_inv c := Subtype.ext ((b.baseChange ℂ).equivFun.apply_symm_apply c)
  right_inv u := Subtype.ext ((b.baseChange ℂ).equivFun.symm_apply_apply u)
  map_add' c d := Subtype.ext ((b.baseChange ℂ).equivFun.symm.map_add c d)
  map_smul' z c := Subtype.ext ((b.baseChange ℂ).equivFun.symm.map_smul z c)

theorem canonicalHolomorphicCoordinateEquiv_repr
    (c : RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b) (i : ι) :
    (b.baseChange ℂ).repr (canonicalHolomorphicCoordinateEquiv V b H hH c) i = c.val i := by
  change (b.baseChange ℂ).equivFun ((b.baseChange ℂ).equivFun.symm c) i = c.val i
  rw [LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CanonicalHolomorphicCoordinates.CM.Construction
