import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.ConormalInclusions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.OverPullbackOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionGlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.SectionTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoordinateSectionMap

/-! # Regular Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.RegularSections

noncomputable section

/-! The coefficient rings on affine special fibers identify with
the original regular sections on the corresponding opens of the
special fiber, compatibly with all literal restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] (X : Over (Spec (.of (DualNumber k))))

def dualAffineReducedOpen (V : X.left.affineOpens) : (ConormalInclusions.dualFamilySpecialFiberObject k X).left.Opens :=
  (VaryingDualReduction.dualFamilyReduction k X) ⁻¹ᵁ V.1

theorem dualAffineCommonOpenInclusion_range (V : X.left.affineOpens) :
    (ConormalInclusions.dualAffineCommonOpenInclusion k X V).left.opensRange = dualAffineReducedOpen k X V := by
  have := Dual.OpenChart.dualFamilyOpenInclusion_open k X V.1
  have h := OverPullbackOpenCover.overPullback_map_opensRange (Smooth.AffineDualProduct.dualBaseReduction k) (Dual.OpenChart.dualFamilyOpenInclusion k X V.1)
  change (ConormalInclusions.dualAffineCommonOpenInclusion k X V).left.opensRange =
    (VaryingDualReduction.dualFamilyReduction k X) ⁻¹ᵁ (Dual.OpenChart.dualFamilyOpenInclusion k X V.1).left.opensRange at h
  exact h.trans (congrArg (fun W => (VaryingDualReduction.dualFamilyReduction k X) ⁻¹ᵁ W) V.1.opensRange_ι)

def dualAffineRegularSectionEquiv (V : X.left.affineOpens) :
    HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (Dual.CommonOpenFiber.dualAffineCommonOpenFiber k X V) ≃+*
      Γ((ConormalInclusions.dualFamilySpecialFiberObject k X).left, dualAffineReducedOpen k X V) :=
  ((IsOpenImmersion.ΓIsoTop (ConormalInclusions.dualAffineCommonOpenInclusion k X V).left).commRingCatIsoToRingEquiv).trans
    (Regular.SectionTransport.regularSectionTransport (dualAffineCommonOpenInclusion_range k X V))

theorem dualAffineRegularSectionEquiv_restrict {V W : X.left.affineOpens} (h : V.1 ≤ W.1)
    (a : HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k (Dual.CommonOpenFiber.dualAffineCommonOpenFiber k X W)) :
    dualAffineRegularSectionEquiv k X V (Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h a) =
      (ConormalInclusions.dualFamilySpecialFiberObject k X).left.presheaf.map
        (homOfLE ((VaryingDualReduction.dualFamilyReduction k X).preimage_mono h)).op (dualAffineRegularSectionEquiv k X W a) := by
  have hR : (ConormalInclusions.dualAffineCommonOpenInclusion k X V).left.opensRange ≤
      (ConormalInclusions.dualAffineCommonOpenInclusion k X W).left.opensRange := by
    rw [dualAffineCommonOpenInclusion_range, dualAffineCommonOpenInclusion_range]
    exact (VaryingDualReduction.dualFamilyReduction k X).preimage_mono h
  have hf : (Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h).left ≫ (ConormalInclusions.dualAffineCommonOpenInclusion k X W).left =
      (ConormalInclusions.dualAffineCommonOpenInclusion k X V).left :=
    congrArg (fun f => f.left) (ConormalInclusions.dualAffineCommonOpenInclusion_natural k X h)
  have hn := ConcreteCategory.congr_hom (Open.ImmersionGlobalSections.openImmersionTopSectionIso_natural
    (Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h).left (ConormalInclusions.dualAffineCommonOpenInclusion k X W).left
    (ConormalInclusions.dualAffineCommonOpenInclusion k X V).left hf hR) a
  have hq : Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h a = (Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h).left.appTop a :=
    Affine.CoordinateSectionMap.affineCoordinateMap_apply k (Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenMap k X h) a
  change Regular.SectionTransport.regularSectionTransport (dualAffineCommonOpenInclusion_range k X V)
      ((IsOpenImmersion.ΓIsoTop (ConormalInclusions.dualAffineCommonOpenInclusion k X V).left).hom
        (Dual.CommonOpenCoefficientRestriction.dualAffineCommonOpenAlgebraMap k X h a)) = _
  rw [hq]
  exact (congrArg (Regular.SectionTransport.regularSectionTransport (dualAffineCommonOpenInclusion_range k X V)) hn).trans
    (Regular.SectionTransport.regularSectionTransport_restrict (dualAffineCommonOpenInclusion_range k X W)
      (dualAffineCommonOpenInclusion_range k X V) hR ((VaryingDualReduction.dualFamilyReduction k X).preimage_mono h) _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualAffine.RegularSections
