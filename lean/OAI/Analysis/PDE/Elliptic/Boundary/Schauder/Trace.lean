import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.Drift

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def secondTrace (D : E →L[ℝ] E →L[ℝ] E) (A : E →L[ℝ] E) : E :=
  ∑ i, D (A (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i)

theorem secondTrace_norm (D : E →L[ℝ] E →L[ℝ] E) (A : E →L[ℝ] E) :
    ‖secondTrace D A‖ ≤ Module.finrank ℝ E * ‖D‖ * ‖A‖ := by
  let b := stdOrthonormalBasis ℝ E
  apply (norm_sum_le _ _).trans
  calc
    (∑ i, ‖D (A (b i)) (b i)‖) ≤
        ∑ _i : Fin (Module.finrank ℝ E), ‖D‖ * ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hn : ‖b i‖ = 1 := b.norm_eq_one i
      have hA := A.le_opNorm (b i)
      have hD := D.le_opNorm (A (b i))
      have hB := (D (A (b i))).le_opNorm (b i)
      rw [hn, mul_one] at hA hB
      exact hB.trans (hD.trans (mul_le_mul_of_nonneg_left hA (norm_nonneg _)))
    _ = Module.finrank ℝ E * ‖D‖ * ‖A‖ := by simp; ring

theorem secondTrace_sub (D H : E →L[ℝ] E →L[ℝ] E) (A B : E →L[ℝ] E) :
    secondTrace D A - secondTrace H B = secondTrace D (A-B) + secondTrace (D-H) B := by
  simp only [secondTrace, sub_apply, map_sub, Finset.sum_sub_distrib]
  abel

theorem secondTrace_variation (D H : E →L[ℝ] E →L[ℝ] E) (A B : E →L[ℝ] E) :
    ‖secondTrace D A - secondTrace H B‖ ≤
      Module.finrank ℝ E * ‖D‖ * ‖A-B‖ + Module.finrank ℝ E * ‖D-H‖ * ‖B‖ := by
  rw [secondTrace_sub]
  exact (norm_add_le _ _).trans (add_le_add (secondTrace_norm _ _) (secondTrace_norm _ _))

theorem composed_secondTrace_variation
    (J K : E →L[ℝ] E) (D H : E →L[ℝ] E →L[ℝ] E) (A B : E →L[ℝ] E) :
    ‖J (secondTrace D A) - K (secondTrace H B)‖ ≤
      ‖J‖ * (Module.finrank ℝ E * ‖D‖ * ‖A-B‖ + Module.finrank ℝ E * ‖D-H‖ * ‖B‖) +
        ‖J-K‖ * (Module.finrank ℝ E * ‖H‖ * ‖B‖) := by
  have hid : J (secondTrace D A) - K (secondTrace H B) =
      J (secondTrace D A - secondTrace H B) + (J-K) (secondTrace H B) := by
    simp only [map_sub, sub_apply]
    abel
  rw [hid]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (J.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (secondTrace_variation D H A B) (norm_nonneg _))
  · exact ((J-K).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (secondTrace_norm H B) (norm_nonneg _))

/-- A quantitative C^α bound for the first-order chart drift, using
only C^α control of the principal coefficient and Lipschitz fixed tensors. -/
theorem secondTrace_holder_bound
    (J : E → E →L[ℝ] E) (D : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] E) {S : Set E} {L N α : ℝ}
    (hL : 0 ≤ L) (_ : 0 ≤ N) (hα1 : α ≤ 1)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    (hJn : ∀ x ∈ S, ‖J x‖ ≤ L) (hDn : ∀ x ∈ S, ‖D x‖ ≤ L)
    (hJh : ∀ x ∈ S, ∀ y ∈ S, ‖J x-J y‖ ≤ L*‖x-y‖)
    (hDh : ∀ x ∈ S, ∀ y ∈ S, ‖D x-D y‖ ≤ L*‖x-y‖)
    (hAn : ∀ x ∈ S, ‖A x‖ ≤ N)
    (hAh : ∀ x ∈ S, ∀ y ∈ S, ‖A x-A y‖ ≤ N*‖x-y‖^α) :
    (∀ x ∈ S, ‖J x (secondTrace (D x) (A x))‖ ≤ Module.finrank ℝ E * L^2 * N) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖J x (secondTrace (D x) (A x)) - J y (secondTrace (D y) (A y))‖ ≤
        3 * Module.finrank ℝ E * L^2 * N * ‖x-y‖^α) := by
  constructor
  · intro x hx
    have hb := ((J x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (secondTrace_norm (D x) (A x)) (norm_nonneg _))
    calc
      _ ≤ ‖J x‖ * (Module.finrank ℝ E * ‖D x‖ * ‖A x‖) := hb
      _ ≤ L * (Module.finrank ℝ E * L * N) := by gcongr; exacts [hJn x hx, hDn x hx, hAn x hx]
      _ = Module.finrank ℝ E * L^2 * N := by ring
  · intro x hx y hy
    have hd : ‖x-y‖ ≤ ‖x-y‖^α :=
      Real.self_le_rpow_of_le_one (norm_nonneg _) (hdiam x hx y hy) hα1
    have hJxy := (hJh x hx y hy).trans (mul_le_mul_of_nonneg_left hd hL)
    have hDxy := (hDh x hx y hy).trans (mul_le_mul_of_nonneg_left hd hL)
    calc
      _ ≤ ‖J x‖ * (Module.finrank ℝ E * ‖D x‖ * ‖A x-A y‖ +
          Module.finrank ℝ E * ‖D x-D y‖ * ‖A y‖) +
          ‖J x-J y‖ * (Module.finrank ℝ E * ‖D y‖ * ‖A y‖) :=
        composed_secondTrace_variation _ _ _ _ _ _
      _ ≤ L * (Module.finrank ℝ E * L * (N*‖x-y‖^α) +
          Module.finrank ℝ E * (L*‖x-y‖^α) * N) +
          (L*‖x-y‖^α) * (Module.finrank ℝ E * L * N) := by
        gcongr
        all_goals first | exact hJn x hx | exact hDn x hx | exact hDn y hy |
          exact hAn y hy | exact hAh x hx y hy
      _ = 3 * Module.finrank ℝ E * L^2 * N * ‖x-y‖^α := by ring

end OAI.Analysis.PDE.Elliptic
