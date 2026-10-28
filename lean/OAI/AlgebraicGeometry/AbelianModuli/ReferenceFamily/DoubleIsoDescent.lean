import OAI.RepresentationTheory.Theta.Geometric.Finite.AbelianFamilyIsoDescent

/-! # Double Iso Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DoubleIsoDescent

noncomputable section

/-! An actual line isomorphism on a constant two-factor family
descends to finitely many parameter coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.RepresentationTheory.Theta.Geometric.Finite.AbelianFamilyIsoDescent

variable (B R : Type) [CommRing B] [CommRing R] [Algebra ℂ B] [Algebra ℂ R]
    [Algebra B R] [IsScalarTower ℂ B R]

theorem doubleParameterFamily_isPullback (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    IsPullback ((RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ X) ▷ Y).left
      ((fst (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⊗ X) Y).left ≫ (fst (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) X).left)
      ((fst (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⊗ X) Y).left ≫ (fst (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B) X).left)
      (Spec.map (CommRingCat.ofHom (algebraMap B R))) :=
  (PELModuli.IntegralModel.Picard.ProductOpenCover.PicardProductOpenCover.productMap_isPullback Y (RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ X)).paste_vert
    (RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap_product_isPullback B R X)

theorem exists_fg_double_family_lineIso (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [QuasiCompact X.hom] [QuasiCompact Y.hom] [Flat X.hom] [Flat Y.hom]
    (L N : HilbertConstruction.Line.Bundles.LineBundle ((Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⊗ X) ⊗ Y).left)
    (a : (L.pullback ((RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ X) ▷ Y).left).sheaf ≅
      (N.pullback ((RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ X) ▷ Y).left).sheaf) :
    ∃ S : Subalgebra B R, S.FG ∧
      Nonempty ((L.pullback ((RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ▷ X) ▷ Y).left).sheaf ≅
        (N.pullback ((RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ▷ X) ▷ Y).left).sheaf) := by
  let T := Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B
  let p := (fst T X).left
  let q := (fst (T ⊗ X) Y).left
  let h := q ≫ p
  have : CompactSpace T.left := inferInstanceAs (CompactSpace (Spec (.of B)))
  have : QuasiCompact p := by
    change QuasiCompact (pullback.fst T.hom X.hom)
    infer_instance
  have : CompactSpace (T ⊗ X).left := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiCompact q := by
    change QuasiCompact (pullback.fst (T ⊗ X).hom Y.hom)
    infer_instance
  have : CompactSpace ((T ⊗ X) ⊗ Y).left := QuasiCompact.compactSpace_of_compactSpace q
  have : Flat p := by
    change Flat (pullback.fst T.hom X.hom)
    infer_instance
  have : Flat q := by
    change Flat (pullback.fst (T ⊗ X).hom Y.hom)
    infer_instance
  have hflat : Flat h := inferInstanceAs (Flat (q ≫ p))
  let HR := doubleParameterFamily_isPullback B R X Y
  let ar := Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo HR.isoPullback.inv
    ((RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ X) ▷ Y).left (RepresentationTheory.Theta.Geometric.ParameterOpenCharts.parameterProjection h R) HR.isoPullback_inv_fst a
  obtain ⟨S, hS, ⟨b⟩⟩ := @RepresentationTheory.Theta.Geometric.Finite.ParameterLineIsoDescent.exists_fg_parameter_lineIso B R _ _ _ ((T ⊗ X) ⊗ Y).left
    (inferInstanceAs (CompactSpace ((T ⊗ X) ⊗ Y).left)) h hflat L N ar
  let HS := doubleParameterFamily_isPullback B S X Y
  exact ⟨S, hS, ⟨Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo HS.isoPullback.hom (RepresentationTheory.Theta.Geometric.ParameterOpenCharts.parameterProjection h S)
    ((RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ▷ X) ▷ Y).left HS.isoPullback_hom_fst b⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DoubleIsoDescent
