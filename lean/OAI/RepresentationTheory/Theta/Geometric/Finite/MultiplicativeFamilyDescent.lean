import OAI.RepresentationTheory.Theta.Geometric.Finite.AbelianFamilyIsoDescent
import OAI.RepresentationTheory.Theta.Geometric.MultiplicativeFamilyBaseChange

/-! # Multiplicative Family Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.MultiplicativeFamilyDescent

noncomputable section

/-! The universal multiplicativity identity descends to a finite
coefficient extension as an actual line-bundle isomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem exists_fg_multiplicative_family_extension
    {B R : Type} [CommRing B] [CommRing R] [Algebra ℂ B] [Algebra ℂ R]
    [Algebra B R] [IsScalarTower ℂ B R]
    {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⊗ A.scheme).left)
    (hL : MultiplicativeFamilyCriterion.IsMultiplicativeFamilyClass A (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ A.scheme).left))) :
    ∃ U : Subalgebra B R, U.FG ∧
      MultiplicativeFamilyCriterion.IsMultiplicativeFamilyClass A (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ U)
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap B U ▷ A.scheme).left)) := by
  let P := A.scheme ⊗ A.scheme
  have : IsProper P.hom := by
    change IsProper (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom)
    infer_instance
  have : Flat P.hom := by
    change Flat (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom)
    infer_instance
  obtain ⟨e⟩ := (MultiplicativeFamilyBaseChange.multiplicativeFamilyBaseChangeIso_iff A L (Complex.AlgebraParameterMap.complexAlgebraParameterMap B R)).mp hL
  obtain ⟨U, hU, he⟩ := AbelianFamilyIsoDescent.exists_fg_constant_family_lineIso P
    (L.pullback (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ◁ (fst A.scheme A.scheme * snd A.scheme A.scheme)).left)
    ((L.pullback (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ◁ fst A.scheme A.scheme).left).tensor
      (L.pullback (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ◁ snd A.scheme A.scheme).left)) e
  exact ⟨U, hU, (MultiplicativeFamilyBaseChange.multiplicativeFamilyBaseChangeIso_iff A L (Complex.AlgebraParameterMap.complexAlgebraParameterMap B U)).mpr he⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.MultiplicativeFamilyDescent
