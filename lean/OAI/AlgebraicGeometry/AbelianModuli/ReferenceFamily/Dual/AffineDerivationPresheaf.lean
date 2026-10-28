import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenDerivationExtension
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.OpenMapLaws
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleHomDerivation

/-! # Affine Derivation Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AffineDerivationPresheaf

noncomputable section

section

/-! The actual affine fiber rings and the linear restriction maps on
their derivations respect identities and successive open restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenFiber.dualCommonOpenFiber CommonOpenFiber.dualAffineCommonOpenFiber

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))

theorem dualAffineCommonOpenMap_id (V : X.left.affineOpens) :
    CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X (le_refl V.1) = 𝟙 (CommonOpenFiber.dualAffineCommonOpenFiber k X V) := by
  change (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (OpenChart.dualFamilyOpenMap k X (le_refl V.1)) = 𝟙 _
  rw [OpenMapLaws.dualFamilyOpenMap_id, CategoryTheory.Functor.map_id]

theorem dualAffineCommonOpenMap_comp {U V W : X.left.affineOpens} (h : U.1 ≤ V.1) (j : V.1 ≤ W.1) :
    CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h ≫ CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X j =
      CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X (h.trans j) := by
  change (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (OpenChart.dualFamilyOpenMap k X h) ≫
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (OpenChart.dualFamilyOpenMap k X j) =
      (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (OpenChart.dualFamilyOpenMap k X (h.trans j))
  rw [← CategoryTheory.Functor.map_comp, OpenMapLaws.dualFamilyOpenMap_comp]

theorem dualAffineCommonOpenAlgebraMap_id (V : X.left.affineOpens) :
    CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X (le_refl V.1) =
      AlgHom.id k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)) := by
  unfold CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap
  rw [dualAffineCommonOpenMap_id, HilbertConstruction.Affine.OverFunctoriality.affineOverMap_id]

theorem dualAffineCommonOpenAlgebraMap_comp {U V W : X.left.affineOpens}
    (h : U.1 ≤ V.1) (j : V.1 ≤ W.1) :
    CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X (h.trans j) =
      (CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h).comp (CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X j) := by
  unfold CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap
  rw [← dualAffineCommonOpenMap_comp k X h j, HilbertConstruction.Affine.OverFunctoriality.affineOverMap_comp]

theorem dualCommonOpenDerivationRestriction_id (V : X.left.affineOpens) :
    CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X (le_refl V.1) = LinearMap.id := by
  have hq := dualAffineCommonOpenAlgebraMap_id k X V
  have he : (AlgHom.id k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V))).toRingHom.Etale :=
    hq ▸ CommonOpenDerivationExtension.dualAffineCommonOpenAlgebraMap_etale k X (le_refl V.1)
  exact (EtaleHomDerivation.etaleAlgHomDerivationLinear_congr _ _ _ he hq).trans (EtaleHomDerivation.etaleAlgHomDerivationLinear_id he)

theorem dualCommonOpenDerivationRestriction_comp {U V W : X.left.affineOpens}
    (h : U.1 ≤ V.1) (j : V.1 ≤ W.1) :
    (CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X h).comp (CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X j) =
      CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X (h.trans j) := by
  have hq := dualAffineCommonOpenAlgebraMap_comp k X h j
  have he : ((CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h).comp
      (CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X j)).toRingHom.Etale :=
    hq ▸ CommonOpenDerivationExtension.dualAffineCommonOpenAlgebraMap_etale k X (h.trans j)
  exact (EtaleHomDerivation.etaleAlgHomDerivationLinear_comp (CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X j)
    (CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h) (CommonOpenDerivationExtension.dualAffineCommonOpenAlgebraMap_etale k X j)
    (CommonOpenDerivationExtension.dualAffineCommonOpenAlgebraMap_etale k X h) he).symm.trans
    (EtaleHomDerivation.etaleAlgHomDerivationLinear_congr _ _ _ he hq).symm

end

/-! The actual special fibers of affine opens form a scheme diagram.
Their transition-derivation modules form a presheaf with the constructed
etale restriction maps. No sheaf or deformation classification is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))

def dualAffineOpenFiberDiagram : X.left.affineOpens ⥤ Over (Spec (.of k)) where
  obj V := CommonOpenFiber.dualAffineCommonOpenFiber k X V
  map f := CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X f.le
  map_id V := dualAffineCommonOpenMap_id k X V
  map_comp f g := (dualAffineCommonOpenMap_comp k X f.le g.le).symm

def dualAffineDerivationPresheaf : X.left.affineOpensᵒᵖ ⥤ ModuleCat k where
  obj V := ModuleCat.of k
    (Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V.unop))
      (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V.unop)))
  map f := ModuleCat.ofHom (CommonOpenDerivationExtension.dualCommonOpenDerivationRestriction k X f.unop.le)
  map_id V := by
    apply ModuleCat.hom_ext
    exact dualCommonOpenDerivationRestriction_id k X V.unop
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact (dualCommonOpenDerivationRestriction_comp k X g.unop.le f.unop.le).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AffineDerivationPresheaf
