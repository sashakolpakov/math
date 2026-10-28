import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLimit
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DoubleIsoDescent

/-! # Double Family Iso Descent -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.DoubleFamilyIsoDescent.Geometric

noncomputable section

/-! Parameter towers and finite descent of actual line isomorphisms
on two-factor families over an arbitrary affine ground scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable (k B R : Type) [CommRing k] [CommRing B] [CommRing R]
    [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

def algebraParameterMap : AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k R ⟶ AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k B :=
  AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecMap k (IsScalarTower.toAlgHom k B R)

theorem algebraParameterMap_product_isPullback (X : Over (Spec (.of k))) :
    IsPullback (algebraParameterMap k B R ▷ X).left (fst (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k R) X).left
      (fst (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k B) X).left (Spec.map (CommRingCat.ofHom (algebraMap B R))) :=
  PELModuli.IntegralModel.Picard.ProductOpenCover.PicardProductOpenCover.productMap_isPullback X (algebraParameterMap k B R)

theorem doubleParameterFamily_isPullback (X Y : Over (Spec (.of k))) :
    IsPullback ((algebraParameterMap k B R ▷ X) ▷ Y).left
      ((fst (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k R ⊗ X) Y).left ≫ (fst (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k R) X).left)
      ((fst (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k B ⊗ X) Y).left ≫ (fst (AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k B) X).left)
      (Spec.map (CommRingCat.ofHom (algebraMap B R))) :=
  (PELModuli.IntegralModel.Picard.ProductOpenCover.PicardProductOpenCover.productMap_isPullback Y (algebraParameterMap k B R ▷ X)).paste_vert
    (algebraParameterMap_product_isPullback k B R X)

theorem exists_fg_double_family_lineIso (X Y : Over (Spec (.of k)))
    [QuasiCompact X.hom] [QuasiCompact Y.hom] [Flat X.hom] [Flat Y.hom]
    (L N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k B ⊗ X) ⊗ Y).left)
    (a : (L.pullback ((algebraParameterMap k B R ▷ X) ▷ Y).left).sheaf ≅
      (N.pullback ((algebraParameterMap k B R ▷ X) ▷ Y).left).sheaf) :
    ∃ S : Subalgebra B R, S.FG ∧
      Nonempty ((L.pullback ((algebraParameterMap k B S ▷ X) ▷ Y).left).sheaf ≅
        (N.pullback ((algebraParameterMap k B S ▷ X) ▷ Y).left).sheaf) := by
  let T := AbelianModuli.ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver k B
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
  let HR := doubleParameterFamily_isPullback k B R X Y
  let ar := Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo HR.isoPullback.inv
    ((algebraParameterMap k B R ▷ X) ▷ Y).left (RepresentationTheory.Theta.Geometric.ParameterOpenCharts.parameterProjection h R) HR.isoPullback_inv_fst a
  obtain ⟨S, hS, ⟨b⟩⟩ := @RepresentationTheory.Theta.Geometric.Finite.ParameterLineIsoDescent.exists_fg_parameter_lineIso B R _ _ _ ((T ⊗ X) ⊗ Y).left
    (inferInstanceAs (CompactSpace ((T ⊗ X) ⊗ Y).left)) h hflat L N ar
  let HS := doubleParameterFamily_isPullback k B S X Y
  exact ⟨S, hS, ⟨Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo HS.isoPullback.hom (RepresentationTheory.Theta.Geometric.ParameterOpenCharts.parameterProjection h S)
    ((algebraParameterMap k B S ▷ X) ▷ Y).left HS.isoPullback_hom_fst b⟩⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.DoubleFamilyIsoDescent.Geometric
