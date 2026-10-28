import Mathlib.Algebra.Module.Equiv.Basic

/-! # Frame Ratios -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.FrameRatios

noncomputable section

/-! Ratios between actual linear frames of a rank-one free module, with their unit and cocycle identities. -/

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

def linearFrameRatio (e f : R ≃ₗ[R] M) : R := e.symm (f 1)

theorem linearFrameRatio_frame (e f : R ≃ₗ[R] M) (r : R) :
    e (linearFrameRatio e f * r) = f r := by
  have he := e.map_smul r (linearFrameRatio e f)
  have hf := f.map_smul r (1 : R)
  exact (congrArg e (mul_comm _ _)).trans (he.trans
    ((congrArg (fun x : M => r • x) (e.apply_symm_apply (f 1))).trans
      (hf.symm.trans (congrArg f (mul_one r)))))

theorem linearFrameRatio_self (e : R ≃ₗ[R] M) : linearFrameRatio e e = 1 := e.symm_apply_apply 1

theorem linearFrameRatio_comp (e f g : R ≃ₗ[R] M) :
    linearFrameRatio e f * linearFrameRatio f g = linearFrameRatio e g := by
  apply e.injective
  exact (linearFrameRatio_frame e f (linearFrameRatio f g)).trans
    ((f.apply_symm_apply (g 1)).trans (e.apply_symm_apply (g 1)).symm)

def linearFrameRatioUnit (e f : R ≃ₗ[R] M) : Rˣ where
  val := linearFrameRatio e f
  inv := linearFrameRatio f e
  val_inv := (linearFrameRatio_comp e f e).trans (linearFrameRatio_self e)
  inv_val := (linearFrameRatio_comp f e f).trans (linearFrameRatio_self f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.FrameRatios
