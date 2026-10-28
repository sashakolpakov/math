import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingCoordinates

/-! # Alternating Differential Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingDifferentialSymmetry

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

theorem orderedToCoefficientCechAlternatingF_comp_d_comp_permutation
    {X : Scheme.{u}} {R : Type u} [CommRing R] (coefficientMap : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 2))) :
    AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
        (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1) ≫
          Permutations.coefficientCechPermutationF coefficientMap M U (n + 1) σ =
      (Equiv.Perm.sign σ : ℤ) •
        (AlternatingExtension.orderedToCoefficientCechAlternatingF coefficientMap M U n ≫
          (Intrinsic.CoefficientCechComplex.coefficientCechComplex coefficientMap M U).d n (n + 1)) := by
  rw [OrderedCech.ComplexProjection.coefficientCechComplex_d_eq_sum_cofaces]
  simp only [comp_sum, sum_comp, comp_zsmul, zsmul_comp,
    Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv σ _ _ fun r => ?_
  rw [Permutations.coefficientCechCoface_comp_permutation]
  rw [← Category.assoc,
    AlternatingExtension.orderedToCoefficientCechAlternatingF_comp_permutation]
  simp only [zsmul_comp, smul_smul]
  rw [Cech.PermutedTupleSigns.cechPermDelete_signed_coefficient]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AlternatingDifferentialSymmetry
