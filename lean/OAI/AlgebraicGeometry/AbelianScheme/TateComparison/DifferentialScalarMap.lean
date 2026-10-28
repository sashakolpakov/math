import OAI.RepresentationTheory.Theta.Geometric.DifferentialNaturality

/-! # Differential Scalar Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.DifferentialScalarMap

noncomputable section

/-! Compare the affine-test differential map with the canonical
coefficient-linear map for an existing algebra tower. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affineComplexMap_surjective (R S : CommAlgCat.{0} ℂ) :
    Function.Surjective (FormConstants.affineComplexMap (R := R) (S := S)) := by
  intro x
  refine ⟨CommAlgCat.ofHom ((Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R S).symm x), ?_⟩
  exact (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R S).apply_symm_apply x

theorem differentialMap_algebra (R S : CommAlgCat.{0} ℂ)
    [Algebra R S] [IsScalarTower ℂ R S] (ω : KaehlerDifferential ℂ R) :
    FormConstants.differentialMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom ℂ R S)) ω =
      KaehlerDifferential.map ℂ ℂ R S ω := by
  have hspan : ω ∈ Submodule.span R (Set.range (KaehlerDifferential.D ℂ R)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hspan using Submodule.span_induction with
  | mem ω h =>
    obtain ⟨a, rfl⟩ := h
    rw [RepresentationTheory.Theta.Geometric.DifferentialNaturality.differentialMap_D, KaehlerDifferential.map_D]
    rfl
  | zero => simp only [map_zero]
  | add a b ha hb hea heb => simp only [map_add, hea, heb]
  | smul r a ha hea =>
    rw [RepresentationTheory.Theta.Geometric.DifferentialNaturality.differentialMap_smul, hea, map_smul]
    exact IsScalarTower.algebraMap_smul S r _

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.DifferentialScalarMap
