import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.ProjectiveEmbeddingDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.SmoothModels

/-! # Smooth Projective Parameters -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SmoothProjectiveParameters

noncomputable section

/-! Smooth projective coefficient parameters for the actual scalar
extension of a fixed finite-presentation source. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.SmoothModels.Coefficients

theorem fixed_smooth_projective_coefficient_model
    (R K : Type) [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K]
    (X : Over (Spec (.of R))) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    [Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X).hom]
    (n : ℕ)
    (i : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ⟶
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n) [IsClosedImmersion i.left] :
    ∃ (s : Finset K)
      (j : (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X ⟶
        AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) n),
      IsClosedImmersion j.left ∧
        Smooth ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X).hom ∧
        IsProper ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X).hom := by
  obtain ⟨s, j, hj⟩ := ProjectiveEmbeddingDescent.fixed_projective_embedding_coefficient_descent R K X hX n i
  let M := (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X
  have : IsClosedImmersion j.left := hj
  have : IsProper M.hom := by rw [← j.w]; infer_instance
  let e := (CoefficientModels.Coefficients.fixedSourceComparison R K s).app X
  have : IsIso e.hom.left := ((Over.forget (Spec (.of K))).mapIso e).isIso_hom
  have : Smooth ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj M).hom := by
    change Smooth ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s) ⋙
      Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K s)).obj X).hom
    rw [← e.hom.w]
    infer_instance
  obtain ⟨t, h, hsm, hp⟩ := Coefficient.SmoothModels.Coefficients.proper_model_eventually_smooth M
  let F := Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
  let a := Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X (CoefficientModels.Coefficients.parameterBaseMap R K s) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R K h)
    (CoefficientModels.Coefficients.parameterBaseMap R K t) (CoefficientModels.Coefficients.coefficient_parameterBaseMap R K h)
  let φ := ((ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientDiagram R K).map (homOfLE h)).hom
  let b := (Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso φ n).symm
  have : IsClosedImmersion (F.map j).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square _ j) hj
  have : IsIso a.inv.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K t)).mapIso a).isIso_inv
  have : IsIso b.hom.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K t)).mapIso b).isIso_hom
  refine ⟨t, a.inv ≫ F.map j ≫ b.hom,
    inferInstanceAs (IsClosedImmersion (a.inv.left ≫ (F.map j).left ≫ b.hom.left)), ?_, ?_⟩
  · have : Smooth (F.obj M).hom := hsm
    rw [← a.inv.w]
    infer_instance
  · have : IsProper (F.obj M).hom := hp
    rw [← a.inv.w]
    infer_instance

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SmoothProjectiveParameters
