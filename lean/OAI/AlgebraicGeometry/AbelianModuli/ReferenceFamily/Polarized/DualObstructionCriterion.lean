import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.PolarizedLevelProduct
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.DualProductTriviality

/-! # Dual Obstruction Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.DualObstructionCriterion

noncomputable section

/-! Vanishing of the actual native structure-sheaf obstruction is
equivalent to triviality of the original polarized full-level deformation.
The forward direction retains a normalized abelian carrier comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {g N : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of (DualNumber ℂ))))

attribute [local instance] Abelian.DualObstructionCriterion.abelianDualFiber_smooth Abelian.DualObstructionCriterion.abelianDualFiber_proper
  Abelian.DualObstructionCriterion.abelianDualFiber_connected Abelian.DualObstructionCriterion.abelianDualFiber_integral Abelian.DualObstructionCriterion.abelianDualH1_complexModule

variable (U : A.abelian.scheme.left.AffineOpenCover)

theorem polarizedDualObstruction_zero_normalizedProduct (h : Dual.ConormalObstructionLinear.dualConormalObstructionLinear A.abelian.scheme U = 0) :
    ∃ e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A ((A.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ)),
      NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e.abelian := by
  obtain ⟨e, he, hm⟩ := (Abelian.DualObstructionCriterion.abelianDualObstruction_zero_iff_groupProduct A.abelian.scheme U).mp h
  exact ⟨@Normalized.PolarizedLevelProduct.normalizedPolarizedLevelProduct g N _ δ A e hm he, he⟩

theorem polarizedDualObstruction_zero_iff_product :
    Dual.ConormalObstructionLinear.dualConormalObstructionLinear A.abelian.scheme U = 0 ↔
      Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A ((A.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).pullback (Smooth.AffineDualProduct.dualBaseProjection ℂ))) := by
  constructor
  · intro h
    obtain ⟨e, _⟩ := polarizedDualObstruction_zero_normalizedProduct A U h
    exact ⟨e⟩
  · rintro ⟨e⟩
    exact (Abelian.DualProductTriviality.abelianDualObstruction_zero_iff_schemeProduct A.abelian.scheme U).mpr ⟨e.abelian⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.DualObstructionCriterion
