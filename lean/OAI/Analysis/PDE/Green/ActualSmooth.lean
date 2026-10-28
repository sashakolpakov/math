import OAI.Analysis.PDE.Green.Physical.Fubini

/-! Smoothness of the actual combined energy in the original three real
extended-time coordinates, with ordinary Euclidean fiber volume. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet
open scoped ContDiff Matrix.Norms.Elementwise

def energyTimeInjectionLinear (n s : ℕ) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s →ₗ[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s where
  toFun := timeInjection n s
  map_add' x y := by
    ext ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [timeInjection]
  map_smul' c x := by
    ext ⟨i, j⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [timeInjection]

theorem contDiff_fiberEmbedding (n s : ℕ) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s =>
      fiberEmbedding n s p.1 p.2) :=
  ((energyTimeInjectionLinear n s).toContinuousLinearMap.contDiff.comp contDiff_fst).add
    ((spatialInjection n s).contDiff.comp contDiff_snd)

def energyComplexTime (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) : ℂ :=
  (z (0, 1) : ℂ) + Complex.I * (z (0, 2) : ℂ)

theorem contDiff_energyComplexTime (k : ℕ∞ω) : ContDiff ℝ k energyComplexTime := by
  have h₁ : ContDiff ℝ k (fun z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 => z (0, 1)) := by fun_prop
  have h₂ : ContDiff ℝ k (fun z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 => z (0, 2)) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp h₁).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h₂))

def physicalEnergyCell (d : ℕ) (a : ℝ) : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :=
  {v | (timeSpaceEquiv (d + 1) 3 v).2 ∈
    physicalSpatialFiber d a (energyComplexTime (timeSpaceEquiv (d + 1) 3 v).1)}

theorem physicalEnergyCell_fiber (d : ℕ) (a : ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
    (fiberEmbedding (d + 1) 3 z) ⁻¹' physicalEnergyCell d a =
      physicalSpatialFiber d a (energyComplexTime z) := by
  ext y
  change (timeSpaceEquiv (d + 1) 3 (fiberEmbedding (d + 1) 3 z y)).2 ∈
      physicalSpatialFiber d a
        (energyComplexTime (timeSpaceEquiv (d + 1) 3 (fiberEmbedding (d + 1) 3 z y)).1) ↔ _
  rw [← timeSpaceEquiv_symm_apply, MeasurableEquiv.apply_symm_apply]

/-- The source energy is smooth on the annulus, not merely a formal density.
Both the moving boundary and the periodic-cell integration have been included. -/
theorem contDiffOn_physicalCombinedEnergy {d : ℕ} (a : ℝ) (ha : 0 < a)
    (e : Fin 3 → Quaternion ℝ) (lam : ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ)}
    (hA : ContDiff ℝ ∞ A) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → ℝ}
    (hB : ContDiff ℝ ∞ B) (hu : ContDiff ℝ ∞ u) :
    ContDiffOn ℝ ∞
      (setFiberCombinedEnergy e lam (physicalEnergyCell d a) A B u)
      {z | a < ‖energyComplexTime z‖} := by
  have h := contDiffOn_real_physical_fiber_integral a ha energyComplexTime
    (contDiff_energyComplexTime ∞)
    (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 =>
      combinedEnergyDensity e lam A B u (fiberEmbedding (d + 1) 3 p.1 p.2))
    ((contDiff_combinedEnergyDensity e lam hA hB hu).comp
      (contDiff_fiberEmbedding (d + 1) 3 ∞))
  have he : setFiberCombinedEnergy e lam (physicalEnergyCell d a) A B u =
      (fun z => ∫ y in physicalSpatialFiber d a (energyComplexTime z),
        combinedEnergyDensity e lam A B u (fiberEmbedding (d + 1) 3 z y)) := by
    funext z
    unfold setFiberCombinedEnergy
    rw [physicalEnergyCell_fiber]
  rw [he]
  exact h

end OAI.Analysis.PDE.Green
