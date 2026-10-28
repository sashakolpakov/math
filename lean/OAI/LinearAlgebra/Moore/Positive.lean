import OAI.LinearAlgebra.Moore.PositiveInverse
import OAI.LinearAlgebra.Moore.ODE

/-! Positivity of the signed Moore determinant on the entire positive cone. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix Set
open scoped MatrixOrder ComplexOrder

theorem complexify_sub {m n : Type*} (A B : Matrix m n (Quaternion ℝ)) :
    complexify (A - B) = complexify A - complexify B := by
  apply Matrix.ext
  intro ⟨i, a⟩ ⟨j, b⟩
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M a b)
    (quaternionMatrixHom.map_sub (A i j) (B i j))

/-- The inverse-trace differential with the inverse expressed entirely in the
ordinary complex representation. No inverse witness remains in the statement. -/
theorem mooreDifferential_eq_complex_inverse {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : D.IsHermitian) :
    mooreDifferential n A D = mooreDet n A *
      (((complexify A)⁻¹ * complexify D).trace.re / 2) := by
  obtain ⟨C, hAC, hCA⟩ := exists_quaternion_inverse_of_complexify_posDef A hA
  have hi : (complexify A)⁻¹ = complexify C := by
    apply Matrix.inv_eq_right_inv
    rw [← complexify_mul, hAC, complexify_one]
  rw [mooreDifferential_inverse n A D C (isHermitian_of_complexify hA.isHermitian)
    hD hAC hCA, hi, ← complexify_mul, complexify_trace_real]
  ring

theorem complex_posDef_segment_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosDef) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((1 - t) • (1 : Matrix ι ι ℂ) + t • A).PosDef := by
  by_cases he : t = 1
  · simpa [he] using hA
  · exact (Matrix.PosDef.one.smul (sub_pos.mpr (lt_of_le_of_ne ht.2 he))).add_posSemidef
      (hA.posSemidef.smul ht.1)

theorem continuousAt_complex_matrix_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosDef) : ContinuousAt Inv.inv A := by
  apply continuousAt_matrix_inv
  have hd : A.det ≠ 0 := hA.det_pos.ne'
  simpa only [Ring.inverse_eq_inv'] using!
    (continuousAt_id.inv₀ hd : ContinuousAt (fun z : ℂ ↦ z⁻¹) A.det)

/-- The Pfaffian-defined, signed Moore determinant is strictly positive for
every positive definite quaternionic Hermitian matrix, in every dimension. -/
theorem mooreDet_pos_of_complexify_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : (complexify A).PosDef) :
    0 < mooreDet n A := by
  let D := A - 1
  let B : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ) := fun t ↦ 1 + t • D
  have hD : D.IsHermitian := (isHermitian_of_complexify hA.isHermitian).sub isHermitian_one
  have hBform (t : ℝ) : complexify (B t) =
      (1 - t) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) + t • complexify A := by
    simp only [B, D, complexify_add, complexify_real_smul, complexify_sub, complexify_one,
      smul_sub, sub_smul, one_smul]
    abel
  have hBpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (complexify (B t)).PosDef := by
    rw [hBform]
    exact complex_posDef_segment_identity hA ht
  have hBcont : Continuous (fun t ↦ complexify (B t)) := by
    simp_rw [hBform]
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  let c : ℝ → ℝ := fun t ↦ (((complexify (B t))⁻¹ * complexify D).trace.re / 2)
  have hc : ContinuousOn c (Icc (0 : ℝ) 1) := by
    intro t ht
    have hi : ContinuousAt (fun s : ℝ ↦ (complexify (B s))⁻¹) t :=
      (continuousAt_complex_matrix_inverse (hBpos t ht)).comp
        (f := fun s : ℝ ↦ complexify (B s)) hBcont.continuousAt
    have htrace : ContinuousAt (fun s : ℝ ↦
        ((complexify (B s))⁻¹ * complexify D).trace) t := by
      exact continuous_id.matrix_trace.continuousAt.comp
        (f := fun s : ℝ ↦ (complexify (B s))⁻¹ * complexify D) (hi.mul continuousAt_const)
    have hr : ContinuousAt (fun s : ℝ ↦
        ((complexify (B s))⁻¹ * complexify D).trace.re) t :=
      Complex.continuous_re.continuousAt.comp
        (f := fun s : ℝ ↦ ((complexify (B s))⁻¹ * complexify D).trace) htrace
    exact (hr.div_const 2).continuousWithinAt
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s ↦ mooreDet n (B s)) (c t * mooreDet n (B t)) t := by
    have hentry (i j : Fin n) : HasDerivAt (fun s ↦ B s i j) (D i j) t := by
      convert! (hasDerivAt_const t ((1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) i j)).add
        ((hasDerivAt_id t).smul_const (D i j)) using 1
      simp
    convert! hasDerivAt_mooreDet_path n B D t hentry using 1
    rw [mooreDifferential_eq_complex_inverse (B t) D (hBpos t ht) hD]
    exact mul_comm _ _
  have hp := positive_of_scalar_linear_ode hc hder
    (show 0 < mooreDet n (B 0) by simp [B, mooreDet_identity])
  simpa [B, D] using hp

end OAI.LinearAlgebra.Moore
