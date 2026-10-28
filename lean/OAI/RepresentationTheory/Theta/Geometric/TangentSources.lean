import OAI.RepresentationTheory.Theta.Geometric.AffineTangents
import OAI.RepresentationTheory.Theta.Geometric.LieFieldTests
import OAI.RepresentationTheory.Theta.Geometric.TangentSourcesBased
import OAI.RepresentationTheory.Theta.Geometric.TangentNeighborhoods

/-! # Tangent Sources -/

namespace OAI.RepresentationTheory.Theta.Geometric.TangentSources

noncomputable section

/-! The affine dual-number tests over an extended coefficient field are
the exact native tests used on the geometric base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k F : Type) [Field k] [Field F] [Algebra k F]

def geometricFieldPointIso : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k F ≅
    (Over.map (LieFieldTests.fieldBaseMap k F)).obj (Over.mk (𝟙 (Spec (.of F)))) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 (Spec (.of F)) ≫ (𝟙 (Spec (.of F)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k F))) = _
    simp only [Category.id_comp]
    rfl)

def geometricDualNumberIso : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k (DualNumber F) ≅ LieFieldTests.extendedDualTest k F :=
  Over.isoMk (Iso.refl (Spec (.of (DualNumber F)))) (by
    change 𝟙 (Spec (.of (DualNumber F))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k F))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber F)))
    rw [Category.id_comp]
    have hr : CommRingCat.ofHom (algebraMap k F) ≫
        CommRingCat.ofHom (algebraMap F (DualNumber F)) =
      CommRingCat.ofHom (algebraMap k (DualNumber F)) :=
      CommRingCat.hom_ext (IsScalarTower.algebraMap_eq k F (DualNumber F)).symm
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap k F))
      (CommRingCat.ofHom (algebraMap F (DualNumber F)))).symm.trans (congrArg Spec.map hr))

theorem geometricAffineOrigin_native :
    (geometricFieldPointIso k F).hom ≫ LieFieldTests.extendedDualOrigin k F =
      AffineTangents.geometricAffineOrigin k F ≫ (geometricDualNumberIso k F).hom := by
  apply Over.OverMorphism.ext
  change 𝟙 (Spec (.of F)) ≫ Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction F)) =
    Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction F)) ≫ 𝟙 (Spec (.of (DualNumber F)))
  simp only [Category.id_comp, Category.comp_id]

def extendedSchemeTangentPoints (X : Over (Spec (.of k)))
    (p : (Over.map (LieFieldTests.fieldBaseMap k F)).obj (Over.mk (𝟙 (Spec (.of F)))) ⟶ X) :=
  {f : LieFieldTests.extendedDualTest k F ⟶ X // LieFieldTests.extendedDualOrigin k F ≫ f = p}

variable (A : Type) [CommRing A] [Algebra k A] [Algebra A F] [IsScalarTower k A F]

def geometricAffineNativeEquiv : AffineTangents.geometricAffineTangentPoints k A F ≃
    extendedSchemeTangentPoints k F (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver k A)
      ((geometricFieldPointIso k F).inv ≫ AffineTangents.geometricAffineBasePoint k A F) :=
  TangentSourcesBased.basedHomEquiv (AffineTangents.geometricAffineOrigin k F) (LieFieldTests.extendedDualOrigin k F)
    (geometricFieldPointIso k F) (geometricDualNumberIso k F)
    (geometricAffineOrigin_native k F) (AffineTangents.geometricAffineBasePoint k A F)

theorem geometricAffineNativeEquiv_apply (f : AffineTangents.geometricAffineTangentPoints k A F) :
    (geometricAffineNativeEquiv k F A f).val = (geometricDualNumberIso k F).inv ≫ f.val :=
  TangentSourcesBased.basedHomEquiv_apply _ _ _ _ _ _ f

omit [Algebra k A] [Algebra A F] [IsScalarTower k A F] in
theorem extendedDualOrigin_surjective : Function.Surjective (LieFieldTests.extendedDualOrigin k F).left :=
  TangentNeighborhoods.dualNumberOrigin_surjective F

omit A [CommRing A] [Algebra k A] [Algebra A F] [IsScalarTower k A F] in
def extendedTangentNeighborhoodEquiv (X U : Over (Spec (.of k)))
    (i : U ⟶ X) [IsOpenImmersion i.left]
    (p : (Over.map (LieFieldTests.fieldBaseMap k F)).obj (Over.mk (𝟙 (Spec (.of F)))) ⟶ U) :
    extendedSchemeTangentPoints k F U p ≃ extendedSchemeTangentPoints k F X (p ≫ i) :=
  TangentNeighborhoods.tangentNeighborhoodEquiv (LieFieldTests.extendedDualOrigin k F) (extendedDualOrigin_surjective k F) i p

end

end OAI.RepresentationTheory.Theta.Geometric.TangentSources
