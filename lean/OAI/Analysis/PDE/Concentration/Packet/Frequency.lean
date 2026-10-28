import OAI.Analysis.PDE.Concentration.Physical.Periodicity

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet

/-- The spatial frequency of a null-coordinate mode in the sector frame. -/
def packetSpatialFrequency {d : ℕ} (κ : ℝ) (v : Fin d → ℝ) : OAI.Analysis.Calculus.Current.SpatialSpace d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin d) => ℝ)).symm
    (fun i => Option.casesOn i (κ * (1 - (∑ j, v j * v j) / 2) / Real.sqrt 2)
      (fun j => κ * v j))

theorem packetSpatialFrequency_phase {d : ℕ} (κ : ℝ) (v : Fin d → ℝ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    OAI.Analysis.Calculus.Current.phaseArgument (OAI.Analysis.Calculus.Current.modeCovector κ v) (nullSpatialShift y) =
      -inner ℝ (packetSpatialFrequency κ v) y := by
  have hi : inner ℝ (packetSpatialFrequency κ v) y =
      y none * (κ * (1 - (∑ j, v j * v j) / 2) / Real.sqrt 2) +
        ∑ j, y (some j) * (κ * v j) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i, y i * packetSpatialFrequency κ v i) = _
    rw [Fintype.sum_option]
    rfl
  rw [hi]
  simp only [OAI.Analysis.Calculus.Current.phaseArgument, OAI.Analysis.Calculus.Current.modeCovector, Fintype.sum_option, nullSpatialShift, OAI.Analysis.Calculus.Current.realPhaseRow]
  have hs : (∑ i, κ * v i * -y (some i)) = -(∑ i, y (some i) * (κ * v i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

/-- Quantization in the dual spatial lattice yields the exact physical
period of the regularized packet current. -/
theorem physicalLatticeCurrent_periodic_of_dual_lattice {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (i : Option (Fin d))
    (hfreq : ∀ j, ∃ k : ℤ, inner ℝ (packetSpatialFrequency (κ j) (v j))
      (R (EuclideanSpace.single i 1)) = (k : ℝ) * (2 * Real.pi) / 100)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    physicalLatticeCurrent R h a κ cR cI v
      (x + physicalSpatialTranslate ((100 : ℝ) • R (EuclideanSpace.single i 1))) =
        physicalLatticeCurrent R h a κ cR cI v x := by
  apply physicalLatticeCurrent_periodic
  intro j
  obtain ⟨k, hk⟩ := hfreq j
  refine ⟨-k, ?_⟩
  rw [packetSpatialFrequency_phase, inner_smul_right, hk]
  push_cast
  ring

end OAI.Analysis.PDE.Concentration
