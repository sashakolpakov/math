import OAI.LinearAlgebra.Moore.Square

/-! Inverse variation and concavity of the logarithmic Moore determinant. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix Filter
open scoped MatrixOrder ComplexOrder Matrix.Norms.Operator Topology

theorem hasDerivAt_complexMatrix_of_entries {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℝ → Matrix I I ℂ) (N : Matrix I I ℂ) (t : ℝ)
    (h : ∀ i j, HasDerivAt (fun s ↦ M s i j) (N i j) t) : HasDerivAt M N t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦
      (h i j).smul_const (Matrix.single i j (1 : ℂ))))
  convert! hd using 1
  · funext s
    ext i j
    simp [Matrix.sum_apply, Matrix.single, ite_and]
  · ext i j
    simp [Matrix.sum_apply, Matrix.single, ite_and]

theorem hasDerivAt_complexMatrix_inverse {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℝ → Matrix I I ℂ) (N : Matrix I I ℂ) (t : ℝ)
    (hdet : (M t).det ≠ 0) (hM : HasDerivAt M N t) :
    HasDerivAt (fun s ↦ (M s)⁻¹) (-((M t)⁻¹ * N * (M t)⁻¹)) t := by
  have hu : IsUnit (M t) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨u, hu⟩ := hu
  have hui : (↑(u⁻¹) : Matrix I I ℂ) = (M t)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  have hd := (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
  rw [hu] at hd
  have hh := hd.comp_hasDerivAt t hM
  change HasDerivAt (fun s ↦ Ring.inverse (M s))
    (-((↑(u⁻¹) : Matrix I I ℂ) * N * (↑(u⁻¹) : Matrix I I ℂ))) t at hh
  rw [hui] at hh
  simpa only [← Matrix.nonsing_inv_eq_ringInverse] using hh

def complexMatrixTraceRealLinear (I : Type*) [Fintype I] : Matrix I I ℂ →ₗ[ℝ] ℝ where
  toFun A := A.trace.re
  map_add' A B := by simp
  map_smul' r A := by simp

def complexMatrixTraceRealCLM (I : Type*) [Fintype I] [DecidableEq I] :
    Matrix I I ℂ →L[ℝ] ℝ := (complexMatrixTraceRealLinear I).toContinuousLinearMap

theorem hasDerivAt_complexInverseTrace {I : Type*} [Fintype I] [DecidableEq I]
    (M D : ℝ → Matrix I I ℂ) (N E : Matrix I I ℂ) (t : ℝ)
    (hdet : (M t).det ≠ 0) (hM : HasDerivAt M N t) (hD : HasDerivAt D E t) :
    HasDerivAt (fun s ↦ ((M s)⁻¹ * D s).trace.re / 2)
      (((M t)⁻¹ * E).trace.re / 2 -
        ((M t)⁻¹ * N * (M t)⁻¹ * D t).trace.re / 2) t := by
  have hd := (hasDerivAt_complexMatrix_inverse M N t hdet hM).mul hD
  have ht := (complexMatrixTraceRealCLM I).hasFDerivAt.comp_hasDerivAt t hd
  have hh := ht.div_const 2
  convert! hh using 1
  change ((M t)⁻¹ * E).trace.re / 2 -
    ((M t)⁻¹ * N * (M t)⁻¹ * D t).trace.re / 2 =
    (-((M t)⁻¹ * N * (M t)⁻¹) * D t + (M t)⁻¹ * E).trace.re / 2
  simp only [Matrix.neg_mul, Matrix.trace_add, Matrix.trace_neg, Complex.add_re, Complex.neg_re]
  ring

theorem complex_inverse_trace_square_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (A D : Matrix I I ℂ) (hA : A.PosDef) (hD : D.IsHermitian) :
    0 ≤ (A⁻¹ * D * A⁻¹ * D).trace.re := by
  have hp : (D * A⁻¹ * D).PosSemidef := by
    have hDe : Dᴴ = D := hD
    simpa only [hDe] using hA.inv.posSemidef.mul_mul_conjTranspose_same D
  simpa only [Matrix.mul_assoc] using complex_trace_mul_nonneg hA.inv.posSemidef hp

def quaternionMatrixEntryLinear (a b : Fin 2) : Quaternion ℝ →ₗ[ℝ] ℂ where
  toFun q := quaternionMatrix q a b
  map_add' p q := by rw [quaternionMatrix_add]; rfl
  map_smul' s q := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M a b) (quaternionMatrix_real_smul s q)
    simpa only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, RingHom.id_apply] using h

def quaternionMatrixEntryCLM (a b : Fin 2) : Quaternion ℝ →L[ℝ] ℂ :=
  (quaternionMatrixEntryLinear a b).toContinuousLinearMap

theorem hasDerivAt_complexify_of_entries {n : ℕ}
    (A : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ)
    (h : ∀ i j, HasDerivAt (fun s ↦ A s i j) (D i j) t) :
    HasDerivAt (fun s ↦ complexify (A s)) (complexify D) t := by
  apply hasDerivAt_complexMatrix_of_entries
  rintro ⟨i, a⟩ ⟨j, b⟩
  exact (quaternionMatrixEntryCLM a b).hasFDerivAt.comp_hasDerivAt t (h i j)

theorem hasDerivAt_log_mooreDet_complexTrace {n : ℕ}
    (A : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ)
    (hA : (complexify (A t)).PosDef) (hD : D.IsHermitian)
    (h : ∀ i j, HasDerivAt (fun s ↦ A s i j) (D i j) t) :
    HasDerivAt (fun s ↦ Real.log (mooreDet n (A s)))
      (((complexify (A t))⁻¹ * complexify D).trace.re / 2) t := by
  have hm := mooreDet_pos_of_complexify_posDef (A t) hA
  convert! (hasDerivAt_mooreDet_path n A D t h).log hm.ne' using 1
  rw [mooreDifferential_eq_complex_inverse (A t) D hA hD]
  field_simp

theorem hasDerivAt_mooreLogSlope {n : ℕ}
    (A D : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (E : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ)
    (hpos : (complexify (A t)).PosDef)
    (hA : ∀ i j, HasDerivAt (fun s ↦ A s i j) (D t i j) t)
    (hD : ∀ i j, HasDerivAt (fun s ↦ D s i j) (E i j) t) :
    HasDerivAt (fun s ↦ ((complexify (A s))⁻¹ * complexify (D s)).trace.re / 2)
      (((complexify (A t))⁻¹ * complexify E).trace.re / 2 -
        ((complexify (A t))⁻¹ * complexify (D t) *
          (complexify (A t))⁻¹ * complexify (D t)).trace.re / 2) t := by
  exact hasDerivAt_complexInverseTrace (fun s ↦ complexify (A s))
    (fun s ↦ complexify (D s)) (complexify (D t)) (complexify E) t hpos.det_pos.ne'
    (hasDerivAt_complexify_of_entries A (D t) t hA)
    (hasDerivAt_complexify_of_entries D E t hD)

/-- The genuine second derivative along a smooth positive Hermitian path.
The last term is the nonnegative quadratic correction responsible for concavity. -/
theorem hasDerivAt_deriv_log_mooreDet_path {n : ℕ}
    (A D : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (E : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ)
    (hpos : (complexify (A t)).PosDef)
    (hA : ∀ i j, HasDerivAt (fun s ↦ A s i j) (D t i j) t)
    (hD : ∀ i j, HasDerivAt (fun s ↦ D s i j) (E i j) t)
    (hlocal : ∀ᶠ s in 𝓝 t, (complexify (A s)).PosDef ∧ (D s).IsHermitian ∧
      ∀ i j, HasDerivAt (fun u ↦ A u i j) (D s i j) s) :
    HasDerivAt (deriv (fun s ↦ Real.log (mooreDet n (A s))))
      (((complexify (A t))⁻¹ * complexify E).trace.re / 2 -
        ((complexify (A t))⁻¹ * complexify (D t) *
          (complexify (A t))⁻¹ * complexify (D t)).trace.re / 2) t := by
  apply (hasDerivAt_mooreLogSlope A D E t hpos hA hD).congr_of_eventuallyEq
  filter_upwards [hlocal] with s hs
  exact (hasDerivAt_log_mooreDet_complexTrace A (D s) s hs.1 hs.2.1 hs.2.2).deriv

theorem deriv_deriv_log_mooreDet_le {n : ℕ}
    (A D : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (E : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ)
    (hpos : (complexify (A t)).PosDef) (hHerm : (D t).IsHermitian)
    (hA : ∀ i j, HasDerivAt (fun s ↦ A s i j) (D t i j) t)
    (hD : ∀ i j, HasDerivAt (fun s ↦ D s i j) (E i j) t)
    (hlocal : ∀ᶠ s in 𝓝 t, (complexify (A s)).PosDef ∧ (D s).IsHermitian ∧
      ∀ i j, HasDerivAt (fun u ↦ A u i j) (D s i j) s) :
    deriv (deriv (fun s ↦ Real.log (mooreDet n (A s)))) t ≤
      ((complexify (A t))⁻¹ * complexify E).trace.re / 2 := by
  rw [(hasDerivAt_deriv_log_mooreDet_path A D E t hpos hA hD hlocal).deriv]
  exact sub_le_self _ (div_nonneg
    (complex_inverse_trace_square_nonneg _ _ hpos (complexify_isHermitian hHerm))
    (by norm_num))

/-- The unnormalized form used when differentiating the nonlinear equation. -/
theorem mooreDifferential_second_derivative_bound {n : ℕ}
    (A D : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (E : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ)
    (hpos : (complexify (A t)).PosDef) (hHerm : (D t).IsHermitian) (hE : E.IsHermitian)
    (hA : ∀ i j, HasDerivAt (fun s ↦ A s i j) (D t i j) t)
    (hD : ∀ i j, HasDerivAt (fun s ↦ D s i j) (E i j) t)
    (hlocal : ∀ᶠ s in 𝓝 t, (complexify (A s)).PosDef ∧ (D s).IsHermitian ∧
      ∀ i j, HasDerivAt (fun u ↦ A u i j) (D s i j) s) :
    mooreDet n (A t) * deriv (deriv (fun s ↦ Real.log (mooreDet n (A s)))) t ≤
      mooreDifferential n (A t) E := by
  rw [mooreDifferential_eq_complex_inverse (A t) E hpos hE]
  exact mul_le_mul_of_nonneg_left
    (deriv_deriv_log_mooreDet_le A D E t hpos hHerm hA hD hlocal)
    (mooreDet_pos_of_complexify_posDef (A t) hpos).le

theorem hasDerivAt_deriv_log_mooreDet_affine {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (t : ℝ) (hD : D.IsHermitian)
    (hpos : (complexify (A + t • D)).PosDef)
    (hlocal : ∀ᶠ s in 𝓝 t, (complexify (A + s • D)).PosDef) :
    HasDerivAt (deriv (fun s ↦ Real.log (mooreDet n (A + s • D))))
      (-((complexify (A + t • D))⁻¹ * complexify D *
          (complexify (A + t • D))⁻¹ * complexify D).trace.re / 2) t := by
  have hentry (s : ℝ) (i j : Fin n) :
      HasDerivAt (fun u ↦ (A + u • D) i j) (D i j) s := by
    convert! (hasDerivAt_const s (A i j)).add ((hasDerivAt_id s).smul_const (D i j)) using 1
    simp
  have hevent : ∀ᶠ s in 𝓝 t, (complexify (A + s • D)).PosDef ∧ D.IsHermitian ∧
      ∀ i j, HasDerivAt (fun u ↦ (A + u • D) i j) (D i j) s := by
    filter_upwards [hlocal] with s hs
    exact ⟨hs, hD, hentry s⟩
  simpa only [complexify_zero, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re,
    zero_div, zero_sub, neg_div] using
    hasDerivAt_deriv_log_mooreDet_path (fun s ↦ A + s • D) (fun _ ↦ D) 0 t
      hpos (hentry t) (fun i j ↦ hasDerivAt_const t (D i j)) hevent

/-- Concavity on every scalar interval contained in the positive cone. -/
theorem concaveOn_log_mooreDet_affine {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (a b : ℝ)
    (hD : D.IsHermitian)
    (hpos : ∀ t ∈ Set.Icc a b, (complexify (A + t • D)).PosDef) :
    ConcaveOn ℝ (Set.Icc a b) (fun t ↦ Real.log (mooreDet n (A + t • D))) := by
  have hfirst (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivAt (fun s ↦ Real.log (mooreDet n (A + s • D)))
        (((complexify (A + t • D))⁻¹ * complexify D).trace.re / 2) t := by
    apply hasDerivAt_log_mooreDet_complexTrace (fun s ↦ A + s • D) D t (hpos t ht) hD
    intro i j
    convert! (hasDerivAt_const t (A i j)).add ((hasDerivAt_id t).smul_const (D i j)) using 1
    simp
  have hsecond (t : ℝ) (ht : t ∈ interior (Set.Icc a b)) :
      HasDerivAt (deriv (fun s ↦ Real.log (mooreDet n (A + s • D))))
        (-((complexify (A + t • D))⁻¹ * complexify D *
          (complexify (A + t • D))⁻¹ * complexify D).trace.re / 2) t := by
    apply hasDerivAt_deriv_log_mooreDet_affine A D t hD (hpos t (interior_subset ht))
    filter_upwards [isOpen_interior.mem_nhds ht] with s hs
    exact hpos s (interior_subset hs)
  apply concaveOn_of_deriv2_nonpos (convex_Icc a b)
    (fun t ht ↦ (hfirst t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hfirst t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hsecond t ht).differentiableAt.differentiableWithinAt)
  intro t ht
  change deriv (deriv (fun s ↦ Real.log (mooreDet n (A + s • D)))) t ≤ 0
  rw [(hsecond t ht).deriv]
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (complex_inverse_trace_square_nonneg _ _
      (hpos t (interior_subset ht)) (complexify_isHermitian hD))) (by norm_num)

theorem convex_complexify_posDef (n : ℕ) :
    Convex ℝ {A : Matrix (Fin n) (Fin n) (Quaternion ℝ) | (complexify A).PosDef} := by
  intro A hA B hB a b ha hb hab
  change (complexify A).PosDef at hA
  change (complexify B).PosDef at hB
  change (complexify (a • A + b • B)).PosDef
  rw [complexify_add, complexify_real_smul, complexify_real_smul]
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_smul, one_smul, zero_add] using hB
  · exact (hA.smul (lt_of_le_of_ne ha (Ne.symm ha0))).add_posSemidef (hB.posSemidef.smul hb)

/-- The logarithm of the signed Pfaffian-defined Moore determinant is concave
on the entire positive quaternionic Hermitian cone. -/
theorem concaveOn_log_mooreDet (n : ℕ) :
    ConcaveOn ℝ {A : Matrix (Fin n) (Fin n) (Quaternion ℝ) | (complexify A).PosDef}
      (fun A ↦ Real.log (mooreDet n A)) := by
  refine ⟨convex_complexify_posDef n, ?_⟩
  intro A hA B hB a b ha hb hab
  have hD : (B - A).IsHermitian :=
    (isHermitian_of_complexify hB.isHermitian).sub (isHermitian_of_complexify hA.isHermitian)
  have hpos (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (complexify (A + t • (B - A))).PosDef := by
    have hh := convex_complexify_posDef n hA hB (sub_nonneg.mpr ht.2) ht.1
      (show (1 - t) + t = 1 by ring)
    have he : (1 - t) • A + t • B = A + t • (B - A) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    rwa [he] at hh
  have hc := concaveOn_log_mooreDet_affine A (B - A) 0 1 hD hpos
  have hh := hc.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp) ha hb hab
  have he : A + b • (B - A) = a • A + b • B := by
    have ha' : a = 1 - b := by linarith
    rw [ha', sub_smul, one_smul, smul_sub]
    abel
  have hAB : A + (B - A) = B := by abel
  simpa only [zero_smul, add_zero, one_smul, hAB,
    smul_eq_mul, mul_zero, mul_one, zero_add, he] using hh

end OAI.LinearAlgebra.Moore
