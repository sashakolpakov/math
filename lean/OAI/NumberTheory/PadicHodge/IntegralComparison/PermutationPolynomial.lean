import Mathlib

/-! # Permutation Polynomial -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.PermutationPolynomial.Characteristic

/-! The characteristic polynomial and trace of the actual permutation action on functions. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι)

def matrix : Matrix ι ι ℤ := fun i j => if σ i = j then 1 else 0

def polynomial : Polynomial ℤ := (matrix σ).charpoly

theorem monic : (polynomial σ).Monic := Matrix.charpoly_monic _

variable (K : Type*) [Field K]

def action : Module.End K (ι → K) where
  toFun f := f ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem action_apply (f : ι → K) (i : ι) : action σ K f i = f (σ i) := rfl

theorem toMatrix : LinearMap.toMatrix (Pi.basisFun K ι) (Pi.basisFun K ι) (action σ K) =
    (matrix σ).map (Int.castRingHom K) := by
  ext i j
  simp [action, matrix, Pi.single_apply, eq_comm]

theorem charpoly : (action σ K).charpoly = (polynomial σ).map (Int.castRingHom K) := by
  calc
    (action σ K).charpoly = (LinearMap.toMatrix (Pi.basisFun K ι)
      (Pi.basisFun K ι) (action σ K)).charpoly :=
        (LinearMap.charpoly_toMatrix (action σ K) (Pi.basisFun K ι)).symm
    _ = (polynomial σ).map (Int.castRingHom K) := by
      rw [Characteristic.toMatrix, Matrix.charpoly_map]
      rfl

theorem trace : LinearMap.trace K (ι → K) (action σ K) =
    ((Finset.univ.filter (fun i => σ i = i)).card : K) := by
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K ι), Characteristic.toMatrix]
  simp [Matrix.trace, Matrix.diag, matrix]

omit [Fintype ι] [DecidableEq ι] in
theorem action_pow (n : ℕ) : action σ K ^ n = action (σ ^ n) K := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, ih]
      apply LinearMap.ext
      intro f
      funext i
      change f (σ ((σ ^ n) i)) = f ((σ ^ (n + 1)) i)
      rw [pow_succ', Equiv.Perm.mul_apply]

theorem trace_pow (n : ℕ) : LinearMap.trace K (ι → K) (action σ K ^ n) =
    ((Finset.univ.filter (fun i => (σ ^ n) i = i)).card : K) := by
  rw [action_pow, Characteristic.trace]

end NumberTheory.PadicHodge.IntegralComparison.PermutationPolynomial.Characteristic

namespace NumberTheory.PadicHodge.IntegralComparison.PermutationPolynomial.Ring

/-! The same integral permutation polynomial computes the action over any commutative ring. -/

variable {ι : Type*} (σ : Equiv.Perm ι) (R : Type*) [CommRing R]

def action : Module.End R (ι → R) where
  toFun f := f ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem action_apply (f : ι → R) (i : ι) : action σ R f i = f (σ i) := rfl

variable [Fintype ι] [DecidableEq ι]

theorem toMatrix : LinearMap.toMatrix (Pi.basisFun R ι) (Pi.basisFun R ι) (action σ R) =
    (Characteristic.matrix σ).map (Int.castRingHom R) := by
  ext i j
  simp [action, Characteristic.matrix, Pi.single_apply, eq_comm]

theorem charpoly : (action σ R).charpoly =
    (Characteristic.polynomial σ).map (Int.castRingHom R) := by
  rw [← LinearMap.charpoly_toMatrix (action σ R) (Pi.basisFun R ι), Ring.toMatrix, Matrix.charpoly_map]
  rfl

end NumberTheory.PadicHodge.IntegralComparison.PermutationPolynomial.Ring

namespace NumberTheory.PadicHodge.IntegralComparison.PermutationPolynomial.Equivalence

/-! Equivariant bijections preserve the actual integral permutation polynomial. -/

variable {ι κ : Type*} (σ : Equiv.Perm ι) (τ : Equiv.Perm κ) (e : ι ≃ κ)
  (h : ∀ i, e (σ i) = τ (e i))

include h in
theorem conjugate : (LinearEquiv.funCongrLeft ℤ ℤ e).conj
    (Ring.action τ ℤ) = Ring.action σ ℤ := by
  apply LinearMap.ext
  intro f
  funext i
  change f (e.symm (τ (e i))) = f (σ i)
  rw [← h, e.symm_apply_apply]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

include h in
theorem polynomial : Characteristic.polynomial σ =
    Characteristic.polynomial τ := by
  have hσ : (Ring.action σ ℤ).charpoly =
      Characteristic.polynomial σ := by
    simpa using Ring.charpoly σ ℤ
  have hτ : (Ring.action τ ℤ).charpoly =
      Characteristic.polynomial τ := by
    simpa using Ring.charpoly τ ℤ
  exact hσ.symm.trans ((congrArg (fun F : Module.End ℤ (ι → ℤ) => F.charpoly)
    (conjugate σ τ e h).symm).trans
      (((LinearEquiv.funCongrLeft ℤ ℤ e).charpoly_conj (Ring.action τ ℤ)).trans hτ))

end NumberTheory.PadicHodge.IntegralComparison.PermutationPolynomial.Equivalence

end

end OAI
