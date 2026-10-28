import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Taylor

/-! Classical finite-order extension from a closed halfspace. -/

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.Calculus.FiniteExtension

open OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniqueDiffOn_positive_halfspace (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1) :
    UniqueDiffOn ℝ {x | 0 ≤ ℓ x} := by
  apply uniqueDiffOn_convex
  · exact convex_halfSpace_ge
      (show IsLinearMap ℝ (fun x => ℓ x) from ⟨ℓ.map_add, ℓ.map_smul⟩) 0
  · refine ⟨ν, ?_⟩
    apply mem_interior_iff_mem_nhds.mpr
    have hopen : IsOpen {x : E | (0 : ℝ) < ℓ x} :=
      isOpen_lt continuous_const ℓ.continuous
    have hmem : ν ∈ {x : E | (0 : ℝ) < ℓ x} := by
      simpa only [Set.mem_ofPred_eq, hν] using (zero_lt_one : (0 : ℝ) < 1)
    refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
    intro x hx
    change 0 ≤ ℓ x
    exact le_of_lt hx

/-- The explicit reflected function is globally Cᴺ and agrees with the
original function on the entire closed positive halfspace. -/
theorem contDiff_extension_of_contDiffOn_halfspace {N : ℕ}
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1) (f : E → F)
    (hf : ContDiffOn ℝ N f {x | 0 ≤ ℓ x}) :
    ContDiff ℝ N (OAI.Analysis.PDE.Schauder.levelGlue ℓ f (reflectedValue (N+1) ℓ ν f)) ∧
      EqOn (OAI.Analysis.PDE.Schauder.levelGlue ℓ f (reflectedValue (N+1) ℓ ν f)) f {x | 0 ≤ ℓ x} := by
  refine ⟨contDiff_finite_reflection ℓ ν hν f _
    (hf.ftaylorSeriesWithin (uniqueDiffOn_positive_halfspace ℓ ν hν)), ?_⟩
  intro x hx
  exact ite_eq_left hx

theorem exists_contDiff_extension_of_contDiffOn_halfspace {N : ℕ}
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1) (f : E → F)
    (hf : ContDiffOn ℝ N f {x | 0 ≤ ℓ x}) :
    ∃ g : E → F, ContDiff ℝ N g ∧ EqOn g f {x | 0 ≤ ℓ x} :=
  ⟨_, contDiff_extension_of_contDiffOn_halfspace ℓ ν hν f hf⟩

end OAI.Analysis.Calculus.FiniteExtension
