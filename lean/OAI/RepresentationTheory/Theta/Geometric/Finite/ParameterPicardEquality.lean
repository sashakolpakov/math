import OAI.RepresentationTheory.Theta.Geometric.Finite.AbelianFamilyIsoDescent
import OAI.RepresentationTheory.Theta.Geometric.Normalized.ParameterClassEquality
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Parameter Picard Equality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterPicardEquality

noncomputable section

/-! Equality in the actual normalized Picard family descends from
an arbitrary parameter algebra to a finitely generated subalgebra. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem exists_fg_parameterPicard_eq
    {B R : Type} [CommRing B] [CommRing R] [Algebra ℂ B] [Algebra ℂ R]
    [Algebra B R] [IsScalarTower ℂ B R]
    {n : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eQ : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    (a b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ P)
    (h : ParameterizedPicardClass.parameterPicardClass Q (Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ≫ a) =
      ParameterizedPicardClass.parameterPicardClass Q (Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ≫ b)) :
    ∃ S : Subalgebra B R, S.FG ∧
      ParameterizedPicardClass.parameterPicardClass Q (Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ≫ a) =
        ParameterizedPicardClass.parameterPicardClass Q (Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ≫ b) := by
  let u := Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B R
  let L := Q.pullback (a ⊗ₘ 𝟙 A.scheme).left
  let N := Q.pullback (b ⊗ₘ 𝟙 A.scheme).left
  have : CompactSpace (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left := inferInstanceAs (CompactSpace (Spec (.of R)))
  have : QuasiSeparatedSpace (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left := inferInstanceAs (QuasiSeparatedSpace (Spec (.of R)))
  have hline := (Normalized.ParameterClassEquality.parameterPicard_eq_iff_lineClass_eq A Q eQ (u ≫ a) (u ≫ b)).mp h
  have he : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (u ▷ A.scheme).left) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (N.pullback (u ▷ A.scheme).left) :=
    (ParameterizedPicardClass.parameterLineClass_naturality Q a u).trans (hline.trans (ParameterizedPicardClass.parameterLineClass_naturality Q b u).symm)
  obtain ⟨e⟩ := Quotient.exact he
  obtain ⟨S, hS, ⟨d⟩⟩ := AbelianFamilyIsoDescent.exists_fg_abelian_family_lineIso A L N e
  have hd : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ▷ A.scheme).left) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (N.pullback (Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ▷ A.scheme).left) := Quotient.sound ⟨d⟩
  refine ⟨S, hS, ?_⟩
  apply congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S)))
  exact (ParameterizedPicardClass.parameterLineClass_naturality Q a (Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B S)).symm.trans
    (hd.trans (ParameterizedPicardClass.parameterLineClass_naturality Q b (Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B S)))

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterPicardEquality
