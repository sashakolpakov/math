import OAI.Analysis.Calculus.Current.Smooth

namespace OAI.Analysis.Calculus.Current

noncomputable section

/-- The actual coordinate-derivative array in the three-slot convention
`(real, i, j)` used by the quaternionic calculus section. -/
def threeSlotMatrixDerivative {d : ℕ}
    (A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) (Quaternion ℝ))
    (x : Index d → ℝ) (z : Index d → ℂ)
    (p : Index d × Fin 3) : Matrix (Index d) (Index d) (Quaternion ℝ) := fun r s =>
  ![quaternionRealD (fun q w => A q w r s) x z p.1,
    quaternionImagD (fun q w => A q w r s) x z p.1 1,
    quaternionImagD (fun q w => A q w r s) x z p.1 Complex.I] p.2

theorem strongDivergence_eq_quaternionDivergence {d : ℕ}
    (A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) (Quaternion ℝ))
    (x : Index d → ℝ) (z : Index d → ℂ) (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (threeSlotMatrixDerivative A x z) b =
      quaternionDivergence (fun a q w => A q w a b) x z := by
  unfold OAI.Analysis.Calculus.Quaternion.strongDivergence quaternionDivergence
  apply Finset.sum_congr rfl
  intro a _
  simp [threeSlotMatrixDerivative, OAI.Analysis.Calculus.Quaternion.threeSlots, Fin.sum_univ_succ, qi, qj]
  ext <;> simp <;> ring

/-- The manuscript's strong-divergence identity for the exact normalized
outer-product wave current, using the actual coordinate derivatives. -/
theorem waveCurrent_strongDivergence {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots
      (threeSlotMatrixDerivative (waveCurrent κ cR cI v) x z) b = 0 := by
  rw [strongDivergence_eq_quaternionDivergence]
  exact waveCurrent_divergence κ cR cI v x z hY b

end
end OAI.Analysis.Calculus.Current
