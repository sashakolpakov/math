import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenCoefficientRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleHomDerivation

/-! # Common Open Derivation Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenDerivationExtension

noncomputable section

/-! The actual open coefficient map is etale. Restricting the overlap
derivation is exactly its uniquely constructed etale extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] CommonOpenFiber.dualCommonOpenFiber CommonOpenFiber.dualAffineCommonOpenFiber CommonOpenCoefficientRestriction.dualAffineCommonOpenMap
attribute [local irreducible] DualOpen.CommonTransitions.dualCommonOpenTransition DualOpen.CommonTransitions.affineChartProductOnOpen Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))
    {V W : X.left.affineOpens} (h : V.1 ≤ W.1)

theorem dualAffineCommonOpenAlgebraMap_etale : (CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h).toRingHom.Etale := by
  have := CommonOpenCoefficientRestriction.dualAffineCommonOpenMap_open k X h
  have := HilbertConstruction.Affine.OverMorphisms.affineOverMap_isOpenImmersion k (CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h)
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (inferInstanceAs (Etale (Spec.map (CommRingCat.ofHom
      (HilbertConstruction.Affine.OverMorphisms.affineOverMap k (CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h)).toRingHom))))

def dualCommonOpenDerivationRestriction :
    Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X W))
        (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X W)) →ₗ[k]
      Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V))
        (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (CommonOpenFiber.dualAffineCommonOpenFiber k X V)) :=
  EtaleHomDerivation.etaleAlgHomDerivationLinear (CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h)
    (dualAffineCommonOpenAlgebraMap_etale k X h)

variable [Smooth X.hom] (U : X.left.AffineOpenCover)

theorem dualCommonOpenDerivation_restrict (i j : U.I₀)
    (hi : W.1 ≤ (U.f i).opensRange) (hj : W.1 ≤ (U.f j).opensRange) :
    dualCommonOpenDerivationRestriction k X h (CommonOpenDerivation.dualCommonOpenDerivation k X U W i j hi hj) =
      CommonOpenDerivation.dualCommonOpenDerivation k X U V i j (h.trans hi) (h.trans hj) := by
  apply Eq.symm
  exact EtaleHomDerivation.etaleAlgHomDerivationLinear_unique (CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h)
    (dualAffineCommonOpenAlgebraMap_etale k X h)
    (CommonOpenDerivation.dualCommonOpenDerivation k X U W i j hi hj)
    (CommonOpenDerivation.dualCommonOpenDerivation k X U V i j (h.trans hi) (h.trans hj))
    (fun a => by
      simpa only [CommonOpenDerivation.dualCommonOpenDerivation, CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap] using
        (CommonOpenCoefficientRestriction.dualCommonOpenDerivation_natural k X h U i j hi hj a).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CommonOpenDerivationExtension
