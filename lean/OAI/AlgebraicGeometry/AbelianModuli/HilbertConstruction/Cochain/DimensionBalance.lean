import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShortComplexDimensionBalance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroKernel

/-! # Dimension Balance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.DimensionBalance

noncomputable section

/-! The dimensions of a nonnegative complex split into homology and adjacent boundary dimensions. -/
open _root_.CategoryTheory
universe u

theorem cochain_dimension_balance_zero {K : Type u} [Field K]
    (D : CochainComplex (ModuleCat.{u} K) ℕ) [Module.Finite K (D.X 0)] :
    Module.finrank K (D.X 0) = Module.finrank K (D.homology 0) +
      Module.finrank K (LinearMap.range (D.d 0 1).hom) := by
  have hd := (D.d 0 1).hom.finrank_range_add_finrank_ker
  have hh := (ZeroKernel.cochainZeroHomologyKernelEquiv D).finrank_eq
  omega

theorem cochain_dimension_balance_succ {K : Type u} [Field K]
    (D : CochainComplex (ModuleCat.{u} K) ℕ) (q : ℕ)
    [Module.Finite K (D.X q)] [Module.Finite K (D.X (q + 1))] :
    Module.finrank K (D.X (q + 1)) = Module.finrank K (D.homology (q + 1)) +
      Module.finrank K (LinearMap.range (D.d q (q + 1)).hom) +
      Module.finrank K (LinearMap.range (D.d (q + 1) (q + 2)).hom) := by
  have hi : (ComplexShape.up ℕ).prev (q + 1) = q :=
    (ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel q (q + 1) by rfl)
  have hk : (ComplexShape.up ℕ).next (q + 1) = q + 2 :=
    (ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel (q + 1) (q + 2) by rfl)
  have hh := (D.homologyIsoSc' q (q + 1) (q + 2) hi hk).toLinearEquiv.finrank_eq
  have : Module.Finite K (D.sc' q (q + 1) (q + 2)).X₁ :=
    (inferInstance : Module.Finite K (D.X q))
  have : Module.Finite K (D.sc' q (q + 1) (q + 2)).X₂ :=
    (inferInstance : Module.Finite K (D.X (q + 1)))
  exact (ShortComplexDimensionBalance.shortComplex_dimension_balance (D.sc' q (q + 1) (q + 2))).trans
    (congrArg (fun n => n + Module.finrank K (LinearMap.range (D.d q (q + 1)).hom) +
      Module.finrank K (LinearMap.range (D.d (q + 1) (q + 2)).hom)) hh.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.DimensionBalance
