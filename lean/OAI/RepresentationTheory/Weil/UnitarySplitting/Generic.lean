import OAI.RepresentationTheory.Weil.UnitarySplitting.TracePairing
import OAI.RepresentationTheory.Weil.UnitarySplitting.NormOneParameters
import OAI.RepresentationTheory.Weil.UnitarySplitting.GenericCharacterCorrection

/-! # Generic -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Generic.Construction

noncomputable section

section

/-! The invertible-difference domain in a unitary group meets every finite
family of right translates. Norm-one scalar matrices give the translates. -/

open _root_.Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (σ : E ≃ₐ[F] E) (Q : Matrix I I E)

omit [Fintype I] [DecidableEq I] in
theorem adjointMatrix_smul (z : E) (A : Matrix I I E) :
    DualPair.Construction.adjointMatrix σ (z • A) = σ z • DualPair.Construction.adjointMatrix σ A := by
  ext i j
  exact map_mul σ z (A j i)

def unitaryScalar (z : E) (hz : σ z * z = 1) : DualPair.Construction.unitaryGroup σ Q := by
  let u := Units.mk0 z (right_ne_zero_of_mul_eq_one hz)
  refine ⟨Units.map (algebraMap E (Matrix I I E)).toMonoidHom u, ?_⟩
  change DualPair.Construction.adjointMatrix σ (algebraMap E (Matrix I I E) z) * Q *
    algebraMap E (Matrix I I E) z = Q
  rw [Algebra.algebraMap_eq_smul_one, adjointMatrix_smul, DualPair.Construction.adjointMatrix_one]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  rw [mul_comm z, hz, one_smul]

theorem unitaryScalar_val (z : E) (hz : σ z * z = 1) :
    ((unitaryScalar σ Q z hz).val : Matrix I I E) = z • 1 :=
  Algebra.algebraMap_eq_smul_one z

def unitaryGenericDomain : Set (DualPair.Construction.unitaryGroup σ Q) :=
  {g | ((g.val : Matrix I I E) - 1).det ≠ 0}

theorem unitary_scalar_difference_det (g : DualPair.Construction.unitaryGroup σ Q) (z : E) (hz : σ z * z = 1) :
    (((g * unitaryScalar σ Q z hz).val : Matrix I I E) - 1).det =
      (g.val : Matrix I I E).det * (↑g.val⁻¹ : Matrix I I E).charpoly.eval z := by
  rw [Matrix.eval_charpoly, ← Matrix.det_mul]
  congr 1
  change (g.val : Matrix I I E) * ((unitaryScalar σ Q z hz).val : Matrix I I E) - 1 =
    (g.val : Matrix I I E) * (Matrix.scalar I z - (↑g.val⁻¹ : Matrix I I E))
  rw [unitaryScalar_val, mul_sub, Units.mul_inv]
  congr 2
  ext i j
  simp [Matrix.scalar, Matrix.diagonal_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one]

theorem unitaryGenericDomain_thick [CharZero F]
    (hσ : Function.Involutive σ) (hne : ∃ z : E, σ z ≠ z) :
    ∀ s : Finset (DualPair.Construction.unitaryGroup σ Q), ∃ t : DualPair.Construction.unitaryGroup σ Q,
      ∀ g ∈ s, g * t ∈ unitaryGenericDomain σ Q := by
  classical
  intro s
  let bad : Finset E := s.biUnion fun g => (↑g.val⁻¹ : Matrix I I E).charpoly.roots.toFinset
  obtain ⟨z, hz, hzbad⟩ := (NormOneParameters.Construction.infinite_normOne σ hσ hne).exists_notMem_finset bad
  refine ⟨unitaryScalar σ Q z hz, fun g hg => ?_⟩
  change (((g * unitaryScalar σ Q z hz).val : Matrix I I E) - 1).det ≠ 0
  rw [unitary_scalar_difference_det]
  apply mul_ne_zero ((Matrix.isUnit_iff_isUnit_det _).mp g.val.isUnit).ne_zero
  intro heval
  apply hzbad
  apply Finset.mem_biUnion.mpr
  refine ⟨g, hg, Multiset.mem_toFinset.mpr ?_⟩
  exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mpr heval

end

/-! Openness of the generic unitary domain. -/

theorem unitaryGenericDomain_open
    {F E : Type} [Field F] [NormedField E] [Algebra F E]
    {I : Type} [Fintype I] [DecidableEq I]
    (σ : E ≃ₐ[F] E) (Q : Matrix I I E) : IsOpen (unitaryGenericDomain σ Q) := by
  change IsOpen {g : DualPair.Construction.unitaryGroup σ Q | ((g.val : Matrix I I E) - 1).det ≠ 0}
  exact isOpen_ne.preimage (by fun_prop)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Generic.Construction
