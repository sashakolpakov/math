import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Taylor

/-! Exact preservation of every prescribed one-sided Taylor jet. -/

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.Calculus.FiniteExtension

open OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_reflection_hasFTaylor {N : ℕ}
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    (f : E → F) (p : E → FormalMultilinearSeries ℝ E F)
    (hp : HasFTaylorSeriesUpToOn N f p {x | 0 ≤ ℓ x}) :
    HasFTaylorSeriesUpTo N (OAI.Analysis.PDE.Schauder.levelGlue ℓ f (reflectedValue (N+1) ℓ ν f))
      (fun x m => OAI.Analysis.PDE.Schauder.levelGlue ℓ (fun y => p y m)
        (fun y => reflectedTaylor (N+1) ℓ ν p y m) x) := by
  apply hasFTaylorSeriesUpTo_levelGlue ℓ ℓ.continuous f _ p _ hp
    (reflectedTaylor_hasFTaylor ℓ ν hν f p hp)
  intro m hm x hx
  exact (reflectedTaylor_boundary (by omega) ℓ ν p hx).symm

/-- The global classical extension has exactly the given derivative
trace, including on the boundary plane. -/
theorem iteratedFDeriv_finite_reflection {N m : ℕ} (hm : m ≤ N)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    (f : E → F) (p : E → FormalMultilinearSeries ℝ E F)
    (hp : HasFTaylorSeriesUpToOn N f p {x | 0 ≤ ℓ x})
    {x : E} (hx : 0 ≤ ℓ x) :
    iteratedFDeriv ℝ m (OAI.Analysis.PDE.Schauder.levelGlue ℓ f (reflectedValue (N+1) ℓ ν f)) x = p x m := by
  have h := (finite_reflection_hasFTaylor ℓ ν hν f p hp).eq_iteratedFDeriv
    (m := m) (by exact_mod_cast hm) x
  simpa only [OAI.Analysis.PDE.Schauder.levelGlue, ite_eq_left hx] using h.symm

end OAI.Analysis.Calculus.FiniteExtension
