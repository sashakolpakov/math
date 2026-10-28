import OAI.Analysis.PDE.Variational.Completion

noncomputable section
namespace OAI.Analysis.PDE.Variational

variable {T H K : Type*} [AddCommGroup T] [Module ℝ T]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [CompleteSpace K]

def completionMap (g : T→ₗ[ℝ]H) (h : T→ₗ[ℝ]K) :
    GradientCompletion g →L[ℝ] GradientCompletion h :=
  completedValue g (testGradient h)

omit [CompleteSpace H] in
theorem completionMap_test (g : T→ₗ[ℝ]H) (h : T→ₗ[ℝ]K)
    (hnorm : ∀ t, ‖h t‖≤‖g t‖) (t : T) :
    completionMap g h (testGradient g t) = testGradient h t := by
  apply completedValue_testGradient (C := 1)
  intro t
  change ‖h t‖≤1*‖g t‖
  simpa only [one_mul] using hnorm t

omit [CompleteSpace H] in
theorem completionMap_norm (g : T→ₗ[ℝ]H) (h : T→ₗ[ℝ]K)
    (hnorm : ∀ t, ‖h t‖=‖g t‖) (u : GradientCompletion g) :
    ‖completionMap g h u‖=‖u‖ := by
  have heq := (denseRange_testGradient g).equalizer
    ((completionMap g h).continuous.norm) continuous_norm
    (funext fun t ↦ by
      rw [Function.comp_apply, completionMap_test g h (fun t ↦ (hnorm t).le)]
      exact hnorm t)
  exact congrFun heq u

theorem completionMap_inverse (g : T→ₗ[ℝ]H) (h : T→ₗ[ℝ]K)
    (hnorm : ∀ t, ‖h t‖=‖g t‖) (u : GradientCompletion g) :
    completionMap h g (completionMap g h u)=u := by
  have heq := (denseRange_testGradient g).equalizer
    ((completionMap h g).continuous.comp (completionMap g h).continuous) continuous_id
    (funext fun t ↦ by
      simp only [Function.comp_apply, completionMap_test g h (fun t ↦ (hnorm t).le),
        completionMap_test h g (fun t ↦ (hnorm t).ge), id_eq])
  exact congrFun heq u

def completionIsometry (g : T→ₗ[ℝ]H) (h : T→ₗ[ℝ]K)
    (hnorm : ∀ t, ‖h t‖=‖g t‖) : GradientCompletion g ≃ₗᵢ[ℝ] GradientCompletion h where
  toLinearEquiv :=
    { (completionMap g h).toLinearMap with
      invFun := completionMap h g
      left_inv := completionMap_inverse g h hnorm
      right_inv := completionMap_inverse h g (fun t ↦ (hnorm t).symm) }
  norm_map' := completionMap_norm g h hnorm

@[simp] theorem completionIsometry_test (g : T→ₗ[ℝ]H) (h : T→ₗ[ℝ]K)
    (hnorm : ∀ t, ‖h t‖=‖g t‖) (t : T) :
    completionIsometry g h hnorm (testGradient g t)=testGradient h t :=
  completionMap_test g h (fun t ↦ (hnorm t).le) t

end OAI.Analysis.PDE.Variational
