import OAI.Analysis.PDE.Weak.Boundary.SupportedRegularity

noncomputable section
open Set _root_.MeasureTheory Filter
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ} {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def supportedDerivativeChoiceOn (Ω K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (k : ℕ)
    (u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))) (i : Fin (m + 1)) :
    Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) := by
  classical
  exact if h : SupportedRegularityOn Ω K (k + 1) u then Classical.choose (h.2 i) else 0

omit [CompleteSpace E] in
theorem supportedDerivativeChoiceOn_spec {Ω K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : SupportedRegularityOn Ω K (k + 1) u) (i : Fin (m + 1)) :
    HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) u (supportedDerivativeChoiceOn Ω K k u i) ∧
      SupportedRegularityOn Ω K k (supportedDerivativeChoiceOn Ω K k u i) := by
  unfold supportedDerivativeChoiceOn
  rw [dite_eq_left hu]
  exact Classical.choose_spec (hu.2 i)

/-- The last-listed derivative is taken first, so adjoining `i` at the front
means taking the actual `i`th weak derivative of the existing word. -/
def weakDerivativeWordOn (Ω K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (k : ℕ)
    (u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))) :
    List (Fin (m + 1)) → Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))
  | [] => u
  | i :: α => supportedDerivativeChoiceOn Ω K (k - (α.length + 1)) (weakDerivativeWordOn Ω K k u α) i

omit [CompleteSpace E] in
theorem weakDerivativeWordOn_regular {Ω K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : SupportedRegularityOn Ω K k u) (α : List (Fin (m + 1))) (hα : α.length ≤ k) :
    SupportedRegularityOn Ω K (k - α.length) (weakDerivativeWordOn Ω K k u α) := by
  induction α with
  | nil => simpa only [weakDerivativeWordOn, List.length_nil, Nat.sub_zero] using hu
  | cons i α ih =>
    have hlt : α.length < k := hα
    have ht : α.length ≤ k := hlt.le
    have heq : k - α.length = k - (α.length + 1) + 1 := by omega
    have hr := ih ht
    rw [heq] at hr
    exact (supportedDerivativeChoiceOn_spec hr i).2

omit [CompleteSpace E] in
theorem supportedRegularityOn_derivative_family {Ω K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))} (hu : SupportedRegularityOn Ω K k u) :
    ∃ U : List (Fin (m + 1)) → Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)), U [] = u ∧
      (∀ α, α.length ≤ k → ∀ᵐ x ∂volume, x ∉ K → U α x = 0) ∧
      (∀ α, α.length < k → ∀ i,
        HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) (U α) (U (i :: α))) := by
  refine ⟨weakDerivativeWordOn Ω K k u, rfl, ?_, ?_⟩
  · intro α hα
    exact (weakDerivativeWordOn_regular hu α hα).support
  · intro α hα i
    have hr := weakDerivativeWordOn_regular hu α hα.le
    have heq : k - α.length = k - (α.length + 1) + 1 := by omega
    rw [heq] at hr
    have hd := (supportedDerivativeChoiceOn_spec hr i).1
    exact hd

end OAI.Analysis.PDE.Weak
