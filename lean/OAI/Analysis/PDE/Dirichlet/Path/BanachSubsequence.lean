import OAI.Analysis.PDE.Dirichlet.Closed.BanachCompactness
import OAI.Analysis.PDE.Dirichlet.Path.Solution

open Set Module Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

theorem exists_densityPath_banach_subsequence {n : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : CoordinateSpace (n + 1) 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α N : ℝ} (hα : 0 < α) (hN : 0 ≤ N)
    (s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁)
    (Φ : SmoothPathSolution e lat r B₀ F₀ F₁ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hΦ : ∀ s, ‖Φ s‖ ≤ N ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ s) x = B₀ x + s.u x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (Φ s) x =
        fderiv ℝ (fun z ↦ B₀ z + s.u z) x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (Φ s) x =
        fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + s.u z)) x) ∧
      LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ s)))) :
    ∃ (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (α / 2)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα.le (Φ (s (φ k)))) atTop (𝓝 g) := by
  let u : ℕ → CoordinateSpace (n + 1) 4 → ℝ := fun k x ↦ B₀ x + (s k).u x
  let f : ℕ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α := fun k ↦ Φ (s k)
  have hu (k) : ContDiff ℝ 2 (u k) := (hB₀.add (s k).smooth).of_le (by norm_num)
  have hper (k) : LatticePeriodic e lat (u k) := hBper.add (s k).periodic
  have hn (k) : ‖f k‖ ≤ N := (hΦ (s k)).1
  have hv (k) (x : {x | r x ≤ 0}) : OAI.Analysis.Normed.Function.Holder.C2Holder.value (f k) x = u k x := (hΦ (s k)).2.1 x
  have hG (k) (x : {x | r x ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (f k) x = fderiv ℝ (u k) x := (hΦ (s k)).2.2.1 x
  have hH (k) (x : {x | r x ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (f k) x = fderiv ℝ (fderiv ℝ (u k)) x := (hΦ (s k)).2.2.2.1 x
  simpa only using! (exists_closed_banach_subsequence
    (E := CoordinateSpace (n + 1) 4) (P := P) (V := V) (ι := ι) (K := K) (r := r)
    (hΩK := hΩK) (α := α) (M := N) e lat hK hr hrper hbounded hreg hα hN u hu hper f hn hv hG hH)

end OAI.Analysis.PDE.Dirichlet
