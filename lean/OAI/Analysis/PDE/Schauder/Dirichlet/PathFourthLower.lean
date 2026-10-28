import OAI.Analysis.PDE.Dirichlet.ThirdHolderHalf
import OAI.Analysis.PDE.Elliptic.Boundary.SubtractedChartHolder
import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.RemainderJets
import OAI.Analysis.Normed.Function.Holder.C2HolderCompactLimit
import OAI.Analysis.PDE.Elliptic.Boundary.PathLowerAssembly

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Elliptic

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
attribute [local instance] OAI.Analysis.PDE.Dirichlet.flG1 OAI.Analysis.PDE.Dirichlet.flS1 OAI.Analysis.PDE.Dirichlet.flG2 OAI.Analysis.PDE.Dirichlet.flS2 OAI.Analysis.PDE.Dirichlet.flG3 OAI.Analysis.PDE.Dirichlet.flS3

/-- All lower chart jets needed by the fourth-order estimate are uniformly
controlled at the compactness exponent, before selecting a path solution. -/
theorem InteriorThirdPathData.uniform_subtracted_chart_jets
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hp₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₀) (hp₁ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (G : E → E) (hG : ContDiff ℝ 4 G)
    {S : Set E} (hS : IsOpen S) (hSc : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (hGK : MapsTo G (closure S) {x | r x ≤ 0}) (hGΩ : MapsTo G S {x | r x < 0}) :
    ∃ N > 0, ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
      OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn (s.u ∘ G) (closure S) (d.exponent/2) N ∧
      ∃ D : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (d.exponent/2),
        (∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x =
          fderiv ℝ (fderiv ℝ (fderiv ℝ (s.u ∘ G))) x) ∧ ‖D‖ ≤ N := by
  have hα : 0 ≤ d.exponent/2 := (half_pos d.exponent_pos).le
  have hα1 : d.exponent/2 ≤ 1 := by linarith [d.exponent_lt_one]
  have hd : 0 < d.normBound := d.normBound_pos
  obtain ⟨R,hR,hthird⟩ := d.uniform_third_holder_fields_half hn e lat hK hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁
  choose T hT hTn using hthird
  let U := fun s => OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf d.exponent_pos.le (d.jets s)
  have hUn (s) : ‖U s‖ ≤ 2*d.normBound :=
    (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_lowerHalf_le_twice d.exponent_pos.le (d.jets s)).trans
      (mul_le_mul_of_nonneg_left (d.jet_norm s) (by norm_num))
  have hU₀ s : ∀ x, OAI.Analysis.Normed.Function.Holder.C2Holder.value (U s) x = B₀ x+s.u x := by
    simpa only [U,OAI.Analysis.Normed.Function.Holder.C2Holder.value_lowerHalf] using d.jet_value s
  have hU₁ s : ∀ x, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (U s) x = fderiv ℝ (fun y => B₀ y+s.u y) x := by
    simpa only [U,OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative_lowerHalf] using d.jet_first s
  have hU₂ s : ∀ x, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (U s) x =
      fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y)) x := by
    simpa only [U,OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_lowerHalf] using d.jet_second s
  obtain ⟨N,hN,hout⟩ := OAI.Analysis.PDE.Elliptic.uniform_subtracted_chart_jets_of_fields hΩK hS hSc hcompact hdiam
    hG hGK hGΩ B₀ hB₀ hα hα1 (by positivity : 0 ≤ 2*d.normBound) hR.le
    (fun s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁ => fun y => B₀ y+s.u y)
    (fun s => (hB₀.add s.smooth).of_le (by norm_num)) U hUn hU₀ hU₁ hU₂ T hTn hT
  refine ⟨N,hN,?_⟩
  intro s
  have hsub : (fun z => (B₀ (G z)+s.u (G z))-B₀ (G z)) = s.u ∘ G := by
    funext z; dsimp only [Function.comp_apply]; ring
  simpa only [hsub] using hout s

end OAI.Analysis.PDE.Schauder
