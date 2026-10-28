import OAI.Analysis.PDE.Dirichlet.Fourth.PathBackground
import OAI.Analysis.Normed.Function.Holder.DirichletFourthExponent

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4

/-- The uniform forcing estimate at the smaller exponent used for compact
families of inverses. This changes only the norm, not the actual source. -/
theorem _root_.OAI.Analysis.PDE.Schauder.InteriorThirdPathData.uniform_second_background_forcing_half
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 5 B₀)
    (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (T S : E → E) (hT : ContDiff ℝ 4 T) (hS : ContDiff ℝ 4 S)
    (hTp : LatticePeriodic e lat T) (hSp : LatticePeriodic e lat S) :
    ∃ C > 0, ∀ s : SmoothPathSolution e lat r B₀ F₀ F₁,
      ∃ F : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := d.exponent/2) e lat,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value F.val x = mooreSecondBackgroundForcing
          (fun y => B₀ y+s.u y) B₀ (densityPath F₀ F₁ s.t) T S x) ∧ ‖F‖ ≤ C := by
  obtain ⟨C,hC,hF⟩ := d.uniform_second_background_forcing hn e lat hK hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁ T S hT hS hTp hSp
  refine ⟨2*C,by positivity,?_⟩
  intro s
  obtain ⟨F,eF,nF⟩ := hF s
  exact ⟨F.lowerHalf d.exponent_pos.le,eF,
    (F.norm_lowerHalf_le_twice d.exponent_pos.le).trans (by linarith only [nF])⟩

end OAI.Analysis.PDE.Dirichlet
