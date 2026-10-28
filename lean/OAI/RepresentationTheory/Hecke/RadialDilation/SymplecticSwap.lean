import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Symplectic Swap -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization

noncomputable section

/-! The position-momentum swap induces an automorphism of the symplectic group. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

theorem coordinateSwap_square : (Theta.PoissonAutomorphyNormalizationData.coordinateSwap (ι := ι) (K := K)) * Theta.PoissonAutomorphyNormalizationData.coordinateSwap = 1 := by
  simp [Theta.PoissonAutomorphyNormalizationData.coordinateSwap, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

omit [Fintype ι] in
theorem coordinateSwap_transpose : (Theta.PoissonAutomorphyNormalizationData.coordinateSwap (ι := ι) (K := K)).transpose = Theta.PoissonAutomorphyNormalizationData.coordinateSwap := by
  simp [Theta.PoissonAutomorphyNormalizationData.coordinateSwap, Matrix.fromBlocks_transpose]

theorem coordinateSwap_J : (Theta.PoissonAutomorphyNormalizationData.coordinateSwap (ι := ι) (K := K)) * Matrix.J ι K * Theta.PoissonAutomorphyNormalizationData.coordinateSwap =
    -Matrix.J ι K := by
  simp [Theta.PoissonAutomorphyNormalizationData.coordinateSwap, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

theorem coordinateSwap_symplectic (g : Theta.PoissonAutomorphyNormalizationData.Sp ι K) :
    Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap ∈ Matrix.symplecticGroup ι K := by
  apply SymplecticGroup.mem_iff'.mpr
  have hcalc : (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap).transpose * Matrix.J ι K *
      (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap) =
      Theta.PoissonAutomorphyNormalizationData.coordinateSwap * (g.val.transpose * (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * Matrix.J ι K * Theta.PoissonAutomorphyNormalizationData.coordinateSwap) * g.val) *
        Theta.PoissonAutomorphyNormalizationData.coordinateSwap := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, coordinateSwap_transpose]
    noncomm_ring
  rw [hcalc, coordinateSwap_J, Matrix.mul_neg, Matrix.neg_mul,
    SymplecticGroup.mem_iff'.mp g.property, Matrix.mul_neg, Matrix.neg_mul,
    coordinateSwap_J, neg_neg]

def symplecticSwapHom : Theta.PoissonAutomorphyNormalizationData.Sp ι K →* Theta.PoissonAutomorphyNormalizationData.Sp ι K where
  toFun g := ⟨Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap, coordinateSwap_symplectic g⟩
  map_one' := by
    apply Subtype.ext
    change Theta.PoissonAutomorphyNormalizationData.coordinateSwap * (1 : Matrix (Sum ι ι) (Sum ι ι) K) * Theta.PoissonAutomorphyNormalizationData.coordinateSwap = 1
    rw [Matrix.mul_one, coordinateSwap_square]
  map_mul' g h := by
    apply Subtype.ext
    change Theta.PoissonAutomorphyNormalizationData.coordinateSwap * (g.val * h.val) * Theta.PoissonAutomorphyNormalizationData.coordinateSwap =
      (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap) * (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * h.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap)
    have heq : (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap) * (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * h.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap) =
        Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * Theta.PoissonAutomorphyNormalizationData.coordinateSwap) * h.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap := by
      noncomm_ring
    rw [heq, coordinateSwap_square, Matrix.mul_one]
    noncomm_ring

def swapPhase (v : Sum ι ι → K) : Sum ι ι → K :=
  Sum.elim (fun i => v (Sum.inr i)) (fun i => v (Sum.inl i))

theorem coordinateSwap_mulVec (v : Sum ι ι → K) :
    Theta.PoissonAutomorphyNormalizationData.coordinateSwap *ᵥ v = swapPhase v := by
  funext i
  cases i <;>
    simp [Theta.PoissonAutomorphyNormalizationData.coordinateSwap, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks, Matrix.one_apply, swapPhase]

omit [Fintype ι] [DecidableEq ι] [CommRing K] in
theorem swapPhase_involutive (v : Sum ι ι → K) : swapPhase (swapPhase v) = v := by
  funext i
  cases i <;> rfl

theorem symplecticSwapHom_action (g : Theta.PoissonAutomorphyNormalizationData.Sp ι K) (v : Sum ι ι → K) :
    (symplecticSwapHom g).val *ᵥ v = swapPhase (g.val *ᵥ swapPhase v) := by
  change (Theta.PoissonAutomorphyNormalizationData.coordinateSwap * g.val * Theta.PoissonAutomorphyNormalizationData.coordinateSwap) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, coordinateSwap_mulVec,
    coordinateSwap_mulVec]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization
