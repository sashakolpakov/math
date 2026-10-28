import OAI.Analysis.PDE.Weak.Elliptic.SupportedRegularity

noncomputable section
open Set _root_.MeasureTheory Filter
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ} {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def supportedDerivativeChoice (K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (k : ℕ)
    (u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))) (i : Fin (m + 1)) :
    Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) := by
  classical
  exact if h : SupportedRegularity K (k + 1) u then Classical.choose (h.2 i) else 0

omit [CompleteSpace E] in
theorem supportedDerivativeChoice_spec {K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : SupportedRegularity K (k + 1) u) (i : Fin (m + 1)) :
    HasWeakDirectionalDerivativeOn volume univ (Pi.single i 1) u (supportedDerivativeChoice K k u i) ∧
      SupportedRegularity K k (supportedDerivativeChoice K k u i) := by
  unfold supportedDerivativeChoice
  rw [dite_eq_left hu]
  exact Classical.choose_spec (hu.2 i)

/-- The last-listed derivative is taken first, so adjoining `i` at the front
means taking the actual `i`th weak derivative of the existing word. -/
def weakDerivativeWord (K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (k : ℕ)
    (u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))) :
    List (Fin (m + 1)) → Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))
  | [] => u
  | i :: α => supportedDerivativeChoice K (k - (α.length + 1)) (weakDerivativeWord K k u α) i

omit [CompleteSpace E] in
theorem weakDerivativeWord_regular {K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : SupportedRegularity K k u) (α : List (Fin (m + 1))) (hα : α.length ≤ k) :
    SupportedRegularity K (k - α.length) (weakDerivativeWord K k u α) := by
  induction α with
  | nil => simpa only [weakDerivativeWord, List.length_nil, Nat.sub_zero] using hu
  | cons i α ih =>
    have hlt : α.length < k := hα
    have ht : α.length ≤ k := hlt.le
    have heq : k - α.length = k - (α.length + 1) + 1 := by omega
    have hr := ih ht
    rw [heq] at hr
    exact (supportedDerivativeChoice_spec hr i).2

omit [CompleteSpace E] in
theorem supportedRegularity_derivative_family {K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))} (hu : SupportedRegularity K k u) :
    ∃ U : List (Fin (m + 1)) → Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)), U [] = u ∧
      (∀ α, α.length ≤ k → ∀ᵐ x ∂volume, x ∉ K → U α x = 0) ∧
      (∀ α, α.length < k → ∀ i,
        HasWeakDirectionalDerivative volume (Pi.single i 1) (U α) (U (i :: α))) := by
  refine ⟨weakDerivativeWord K k u, rfl, ?_, ?_⟩
  · intro α hα
    exact (weakDerivativeWord_regular hu α hα).support
  · intro α hα i
    have hr := weakDerivativeWord_regular hu α hα.le
    have heq : k - α.length = k - (α.length + 1) + 1 := by omega
    rw [heq] at hr
    have hd := (supportedDerivativeChoice_spec hr i).1
    intro φ hφ hs
    exact hd φ hφ hs (subset_univ _)

end OAI.Analysis.PDE.Weak
