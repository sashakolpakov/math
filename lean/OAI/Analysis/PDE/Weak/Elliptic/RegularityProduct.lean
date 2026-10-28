import OAI.Analysis.PDE.Weak.Elliptic.Regularity
import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded

noncomputable section
open Set _root_.MeasureTheory Filter
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Smooth coefficient multiplication preserves every finite order of
actual local weak L² regularity. -/
theorem WeakRegularity.operator_mul
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω k u)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → E →L[ℝ] F) (hA : SmoothBounded A)
    {M : ℝ} (hM : ∀ x, ‖A x‖ ≤ M) :
    WeakRegularity Ω k
      (fieldMultiplierCLM A hA.1.continuous.aestronglyMeasurable (Eventually.of_forall hM) u) := by
  induction k generalizing A u M with
  | zero => trivial
  | succ k ih =>
    intro i
    obtain ⟨g, hd, hg⟩ := hu i
    have hAi : SmoothBounded (coordinateDerivative A i) := hA.partial i
    obtain ⟨D, hD⟩ := hAi.bound
    let ag := fieldMultiplierCLM A hA.1.continuous.aestronglyMeasurable
      (Eventually.of_forall hM) g
    let du := fieldMultiplierCLM (coordinateDerivative A i) hAi.1.continuous.aestronglyMeasurable
      (Eventually.of_forall hD) u
    refine ⟨ag + du, ?_, ?_⟩
    · have hr := hd.operator_apply volume A (hA.1.of_le (by simp)) u g
      apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on volume hr
      · filter_upwards [fieldMultiplierCLM_ae A hA.1.continuous.aestronglyMeasurable
          (Eventually.of_forall hM) u] with x hx
        exact fun _ ↦ hx.symm
      · filter_upwards [fieldMultiplierCLM_ae A hA.1.continuous.aestronglyMeasurable
          (Eventually.of_forall hM) g,
          fieldMultiplierCLM_ae (coordinateDerivative A i) hAi.1.continuous.aestronglyMeasurable
            (Eventually.of_forall hD) u, Lp.coeFn_add ag du] with x hx hy hz
        intro _
        rw [hz]
        change A x (g x) + fderiv ℝ A x (Pi.single i 1) (u x) = ag x + du x
        rw [hx, hy]
        rfl
    · exact (ih (u := g) hg A hA hM).add
        (ih (u := u) hu.pred (coordinateDerivative A i) hAi hD)

end OAI.Analysis.PDE.Weak
