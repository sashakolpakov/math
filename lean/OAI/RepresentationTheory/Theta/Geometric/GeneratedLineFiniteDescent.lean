import OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterLimit
import OAI.RepresentationTheory.Theta.Geometric.Picard.PicardPullback
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GeneratedComplexMap
import OAI.RepresentationTheory.Theta.Geometric.ConstantFamilyGeneratedTwist
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective

/-! # Generated Line Finite Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.GeneratedLineFiniteDescent

noncomputable section

/-! A globally generated line bundle on an arbitrary constant family
descends through its actual projective-space classifying morphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

attribute [local instance] AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup

variable {R : Type} [CommRing R] [Algebra ℂ R]

theorem exists_fg_generated_family_line
    (A : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [QuasiCompact A.hom] [QuasiSeparated A.hom]
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⊗ A).left)
    (hL : AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators.HasFiniteGlobalGenerators L.sheaf) :
    ∃ S : Subalgebra ℂ R, S.FG ∧ ∃ N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S ⊗ A).left,
      Nonempty ((N.pullback (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A).left).sheaf ≅ L.sheaf) := by
  obtain ⟨n, a, ha, ⟨eL⟩⟩ := AlgebraicGeometry.SheafCohomology.Projective.GeneratedComplexMap.generated_exists_complex_projective_map
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⊗ A).hom L hL
  let P := Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let : LocallyOfFiniteType (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := (AlgebraicGeometry.Foundations.Scheme.ClosedProjective.projectiveSpaceToBase_finiteType n).1
  let : IsLocallyNoetherian AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := inferInstance
  let : LocallyOfFinitePresentation P.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
  obtain ⟨S, hS, b, hb⟩ := Finite.ParameterLimit.exists_fg_constant_family_morphism A P (Over.homMk a ha)
  let H := AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := ℂ) (0 : Fin (n + 1))
  refine ⟨S, hS, H.pullback b.left, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A).left b.left).app H.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hb)).app H.sheaf ≪≫ eL

theorem exists_fg_family_line_of_generated_twist
    (A : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [QuasiCompact A.hom] [QuasiSeparated A.hom]
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⊗ A).left) (H : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hL : AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators.HasFiniteGlobalGenerators
      (L.tensor (H.pullback (snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left)).sheaf) :
    ∃ S : Subalgebra ℂ R, S.FG ∧ ∃ N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S ⊗ A).left,
      Nonempty ((N.pullback (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A).left).sheaf ≅ L.sheaf) := by
  obtain ⟨S, hS, N, eN⟩ := exists_fg_generated_family_line A
    (L.tensor (H.pullback (snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left)) hL
  let f := (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A).left
  let pS := (snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S) A).left
  let pR := (snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left
  have hp : f ≫ pS = pR := congrArg Over.Hom.left
    (whiskerRight_snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val) A)
  obtain ⟨M, hM⟩ := Quotient.exists_rep (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N *
    (Picard.PicardPullback.picardPullback pS (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf H))⁻¹)
  refine ⟨S, hS, M, ?_⟩
  suffices h : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback f) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L from Quotient.exact h
  have hN : Picard.PicardPullback.picardPullback f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * Picard.PicardPullback.picardPullback pR (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf H) := Quotient.sound eN
  change Picard.PicardPullback.picardPullback f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M = _ at hM
  rw [hM, map_mul, map_inv, Picard.PicardPullback.picardPullback_comp, hp, hN, mul_inv_cancel_right]

theorem exists_fg_projective_family_line
    (A : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [QuasiCompact A.hom] [QuasiSeparated A.hom]
    {n : ℕ} (e : A.left ⟶ Projective.Map.RelativeProjective.projectiveSpace ℂ n) [IsClosedImmersion e]
    (he : e ≫ Projective.Map.RelativeProjective.projectiveSpaceToBase ℂ n = A.hom)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⊗ A).left) :
    ∃ S : Subalgebra ℂ R, S.FG ∧ ∃ N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S ⊗ A).left,
      Nonempty ((N.pullback (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A).left).sheaf ≅ L.sheaf) := by
  obtain ⟨H, hH⟩ := ConstantFamilyGeneratedTwist.exists_constant_family_generated_twist A e he R L
  exact exists_fg_family_line_of_generated_twist A L H hH

theorem exists_fg_abelian_family_line (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    [QuasiCompact A.toOver.hom] [QuasiSeparated A.toOver.hom]
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⊗ A.toOver).left) :
    ∃ S : Subalgebra ℂ R, S.FG ∧ ∃ N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S ⊗ A.toOver).left,
      Nonempty ((N.pullback (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A.toOver).left).sheaf ≅ L.sheaf) := by
  obtain ⟨n, e, he, hb⟩ := A.exists_closedImmersion
  let := he
  exact exists_fg_projective_family_line A.toOver e hb L

end

end OAI.RepresentationTheory.Theta.Geometric.GeneratedLineFiniteDescent
