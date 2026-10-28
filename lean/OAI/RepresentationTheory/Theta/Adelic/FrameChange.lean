import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Frame Change -/

namespace OAI.RepresentationTheory.Theta.Adelic.FrameChange

noncomputable section

/-! Changing between two symplectic frames of the same actual trace tensor
space conjugates its concrete matrix action. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction

variable {k : Type*} [Field k] {d : k} {n m : ℕ}
    {H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)}
    {K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)}
    (c e : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H K)

def frameChangeLinear : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m ≃ₗ[k] Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m :=
  c.coordinates.symm.trans e.coordinates

theorem frameChange_preserves (x y : Weil.AdelicSplitting.TensorSpace.Construction.StandardPhase (k := k) n m) :
    Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing n m (frameChangeLinear c e x) (frameChangeLinear c e y) =
      Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing n m x y := by
  change Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing n m (e.coordinates (c.coordinates.symm x))
    (e.coordinates (c.coordinates.symm y)) = _
  rw [e.preserves, ← c.preserves]
  simp

def frameChange : Matrix.symplecticGroup (Fin (n * m)) k := by
  refine ⟨LinearMap.toMatrix' (frameChangeLinear c e).toLinearMap, ?_⟩
  apply SymplecticGroup.mem_iff'.mpr
  apply Matrix.toBilin'.injective
  rw [← Matrix.toBilin'_comp]
  simp only [Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have h := congrArg (fun a : k => -a) (frameChange_preserves c e x y)
  simpa [Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing] using h

theorem frameChange_intertwines (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) :
    frameChange c e * Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K c g =
      Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K e g * frameChange c e := by
  apply Subtype.ext
  apply LinearMap.toMatrix'.symm.injective
  ext x i
  simp [frameChange, frameChangeLinear, Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic,
    Weil.AdelicSplitting.TensorSpace.Construction.coordinateMatrix, Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction]

theorem frameChange_conjugates (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) :
    frameChange c e * Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K c g * (frameChange c e)⁻¹ =
      Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H K e g := by
  rw [frameChange_intertwines]
  exact mul_inv_cancel_right _ _

end

end OAI.RepresentationTheory.Theta.Adelic.FrameChange
