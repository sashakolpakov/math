import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Presheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf

/-! # Power Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerSplitting

noncomputable section

/-! Split the actual finite tensor product into its first n factors
and its last factor. This is the sectionwise comparison needed for
arbitrary pullback of the original tensor-power sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

def tensorFinSuccSplit (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ) :
    (⨂[R] (_ : Fin (n + 1)), M) ≃ₗ[R] (⨂[R] (_ : Fin n), M) ⊗[R] M :=
  (PiTensorProduct.reindex R (fun _ : Fin (n + 1) => M) finSumFinEquiv.symm).trans
    ((PiTensorProduct.tmulEquiv R M).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R _) (PiTensorProduct.subsingletonEquiv (0 : Fin 1))))

theorem tensorFinSuccSplit_tprod (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (v : Fin (n + 1) → M) :
    tensorFinSuccSplit R M n (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun i : Fin n => v i.castSucc) ⊗ₜ[R] v (Fin.last n) := by
  simp only [tensorFinSuccSplit, LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod,
    Equiv.symm_symm, PiTensorProduct.tmulEquiv_symm_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerSplitting
