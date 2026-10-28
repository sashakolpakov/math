import OAI.NumberTheory.ArithmeticGroups.Lattices.SpectralOperatorExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingSymmetricWeights

/-! # Conjugation Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.ConjugationCoordinates.Construction

noncomputable section

/-! Conjugation by a split exponential rescales matrix coordinates
by the exponential of the corresponding weight difference. -/

open _root_.ContinuousLinearMap NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem symmetric_operator_exp_isSymmetric
    (A : L →L[ℝ] L) (hA : A.toLinearMap.IsSymmetric) : (exp A).toLinearMap.IsSymmetric := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have he : adjoint (exp A) = exp A := (show IsSelfAdjoint A from hA.clm_adjoint_eq).exp
  exact (eq_adjoint_iff _ _).mp he.symm

theorem exp_smul_apply_eigenbasis
    {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (H : L →L[ℝ] L)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i) (t : ℝ) (i : Fin m) :
    exp (t • H) (b i) = Real.exp (t * w i) • b i := by
  apply SpectralOperatorExponential.Construction.exp_apply_eigenbasis b (fun j => t * w j) (t • H)
  intro j
  rw [smul_apply, heig, smul_smul]

theorem split_exponential_conjugation_coordinate
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (t : ℝ) (X : L →L[ℝ] L) (i j : Fin m) :
    b.repr ((exp ((-t) • H) * X * exp (t • H)) (b j)) i =
      Real.exp (t * (w j - w i)) * b.repr (X (b j)) i := by
  have hs : (exp ((-t) • H)).toLinearMap.IsSymmetric :=
    symmetric_operator_exp_isSymmetric _ (hH.smul (by simp))
  have hp (j : Fin m) : exp (t • H) (b j) = Real.exp (t * w j) • b j :=
    exp_smul_apply_eigenbasis b.toBasis H w heig t j
  have hn (j : Fin m) : exp ((-t) • H) (b j) = Real.exp ((-t) * w j) • b j :=
    exp_smul_apply_eigenbasis b.toBasis H w heig (-t) j
  change b.repr (exp ((-t) • H) (X (exp (t • H) (b j)))) i = _
  rw [hp]
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul]
  rw [CommutingSymmetricWeights.Construction.orthonormal_eigen_coordinate b _ hs (fun s => Real.exp ((-t) * w s)) hn]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.ConjugationCoordinates.Construction
