import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SmoothProjectiveParameters
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.CoefficientSpecialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ProjectivePresentation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components

/-! # Fixed Projective -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FixedProjective

noncomputable section

/-! An actual arithmetic scheme with smooth projective complex fiber
acquires smooth projective geometry by a constructed arithmetic base change. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem arithmetic_fixed_smooth_projective_model
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) [Algebra B.R ℂ]
    (hAlg : algebraMap B.R ℂ = B.embedding.comp B.toField)
    (X : Over B.base) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    [Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).obj X).hom]
    (n : ℕ)
    (i : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).obj X ⟶
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ n) [IsClosedImmersion i.left]
    (N : ℕ) (hN : N ≠ 0) :
    ∃ D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      N ∣ D.denominator ∧ ∃ φ : B.R →+* D.R,
        D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField ∧
        Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).hom ∧
        IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).hom ∧
        Components.RelativelyProjective ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X) := by
  obtain ⟨s, j, hj, hsm, hp⟩ := Fixed.SmoothProjectiveParameters.fixed_smooth_projective_coefficient_model B.R ℂ X hX n i
  obtain ⟨D, hdiv, ψ, _, hψ⟩ :=
    B.coefficient_parameter_integral_specialization hAlg s 1 one_ne_zero N hN
  let φ := ψ.comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s))
  let b := Spec.map (CommRingCat.ofHom ψ)
  let c := Spec.map (CommRingCat.ofHom φ)
  have hbc : b ≫ Fixed.CoefficientModels.Coefficients.parameterBaseMap B.R ℂ s = c := by
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s)))
      (CommRingCat.ofHom ψ)).symm
  let F := Over.pullback b
  let M := (Over.pullback (Fixed.CoefficientModels.Coefficients.parameterBaseMap B.R ℂ s)).obj X
  let a := Group.BaseChangeComparisons.GroupBaseChange.iteratedIso X (Fixed.CoefficientModels.Coefficients.parameterBaseMap B.R ℂ s) b c hbc
  let p := (Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso ψ n).symm
  have : Smooth M.hom := hsm
  have : IsProper M.hom := hp
  have : Smooth (F.obj M).hom := inferInstanceAs (Smooth (pullback.snd M.hom b))
  have : IsProper (F.obj M).hom := inferInstanceAs (IsProper (pullback.snd M.hom b))
  have : IsClosedImmersion j.left := hj
  have : IsClosedImmersion (F.map j).left := MorphismProperty.of_isPullback (Specialization.base_change_square b j) hj
  have : IsIso a.inv.left := ((Over.forget D.base).mapIso a).isIso_inv
  have : IsIso p.hom.left := ((Over.forget D.base).mapIso p).isIso_hom
  let k := a.inv ≫ F.map j ≫ p.hom
  have : IsClosedImmersion k.left :=
    inferInstanceAs (IsClosedImmersion (a.inv.left ≫ (F.map j).left ≫ p.hom.left))
  refine ⟨D, hdiv, φ, hψ, ?_, ?_, ⟨Affine.ProjectivePresentation.affine_projective_relative_presentation n k⟩⟩
  · rw [← a.inv.w]
    infer_instance
  · rw [← a.inv.w]
    infer_instance

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FixedProjective
