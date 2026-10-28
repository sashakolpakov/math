import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.DualObstructionCriterion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.IsoReidentifiedFiber

/-! # Dual Product Triviality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.DualProductTriviality

noncomputable section

/-! The native obstruction vanishes exactly for scheme products.
An arbitrary product comparison can be normalized on its special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (X : Over (Spec (.of (DualNumber ℂ)))) [GrpObj X] [IsCommMonObj X]
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]

attribute [local instance] DualObstructionCriterion.abelianDualFiber_smooth DualObstructionCriterion.abelianDualFiber_proper
  DualObstructionCriterion.abelianDualFiber_connected DualObstructionCriterion.abelianDualFiber_integral DualObstructionCriterion.abelianDualH1_complexModule

theorem abelianDualObstruction_zero_iff_schemeProduct (U : X.left.AffineOpenCover) :
    Dual.ConormalObstructionLinear.dualConormalObstructionLinear X U = 0 ↔
      Nonempty (X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) := by
  constructor
  · intro h
    obtain ⟨e, _, _⟩ := (DualObstructionCriterion.abelianDualObstruction_zero_iff_groupProduct X U).mp h
    exact ⟨e⟩
  · rintro ⟨e⟩
    apply (Dual.ConormalObstructionLinear.dualConormalObstructionLinear_zero_iff_product X U).mpr
    exact ⟨Product.IsoReidentifiedFiber.productIsoCanonicalFiber (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ))
      (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso ℂ) X
        (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X) e,
      Product.IsoReidentifiedFiber.productIsoCanonicalFiber_normalized (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ))
        (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso ℂ) X
          (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X) e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.DualProductTriviality
