import OAI.Analysis.PDE.Dirichlet.ThirdHolderHalf

noncomputable section
open Set Module
open scoped ContDiff BoundedContinuousFunction
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Elliptic

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
attribute [local instance] flG1 flS1 flG2 flS2 flG3 flS3 flG4 flS4

/-- With the data-only third-order estimate already proved, uniform actual
fourth-order Hölder bounds suffice for closed C⁴ regularity of every Banach
path limit. The limit's original C² Hölder exponent is arbitrary. -/
theorem BanachPathLimit.contDiffOn_four_closed_of_uniform_fourth
    (hn : 1 ≤ n) {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    {β t : ℝ} {s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁}
    (L : BanachPathLimit e lat r B₀ F₀ F₁ hΩK β s t)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x=0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hfourth : ∃ M > 0, ∀ a : SmoothPathSolution e lat r B₀ F₀ F₁,
      OAI.Analysis.PDE.Elliptic.HasFourthHolderBound {x | r x ≤ 0} (d.exponent/2) (fun y => B₀ y+a.u y) M) :
    ContDiffOn ℝ 4 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) {x | r x ≤ 0} := by
  obtain ⟨R,hR,hthird⟩ := d.uniform_third_holder_fields_half hn e lat hK hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁
  obtain ⟨M,hM,hfourth⟩ := hfourth
  exact L.contDiffOn_four_closed_of_holder_fields hn d (hr.of_le (by simp)) hB₀ hreg
    (half_pos d.exponent_pos) hR.le hM.le hthird hfourth

end OAI.Analysis.PDE.Dirichlet
