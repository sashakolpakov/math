import OAI.Analysis.HodgeTheory.Decomposition.LocalLaplacianBoundary

/-! # Local Laplacian Locality -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalLaplacianLocality.Constructions

noncomputable section

/-! Local equality of coefficient fields determines their Kähler-bracket
Laplacian, with no assumption about values outside the chart domain. -/

open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem extDeriv_congr_of_eventuallyEq (n : ℕ) {a b : E → DifferentialForms.Manifold.Basic.FormValue E n} {x : E}
    (h : a =ᶠ[𝓝 x] b) : extDeriv a x = extDeriv b x := by
  have hh := ExteriorConstantBracket.Constructions.directionalExteriorDerivative_congr n (ContinuousLinearMap.id ℝ E) h
  simpa only [ExteriorConstantBracket.Constructions.directionalExteriorDerivative_id] using hh

theorem localLefschetzLaplacian_eqOn (n : ℕ) (J : E →L[ℝ] E)
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (K2 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1))
    {a b : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)} {U : Set E} (hU : IsOpen U)
    (hab : Set.EqOn a b U) {x : E} (hx : x ∈ U) :
    LocalLaplacianBoundary.Constructions.localLefschetzLaplacian n J K0 K1 K2 a x = LocalLaplacianBoundary.Constructions.localLefschetzLaplacian n J K0 K1 K2 b x := by
  have heq (y : E) (hy : y ∈ U) : a =ᶠ[𝓝 y] b := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact hab hz
  have hB : ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n J K1 K0 a =ᶠ[𝓝 x] ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n J K1 K0 b := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_congr n J K1 K0 (heq y hy)
  have hd : extDeriv a =ᶠ[𝓝 x] extDeriv b := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact extDeriv_congr_of_eventuallyEq (n + 1 + 1) (heq y hy)
  rw [LocalLaplacianBoundary.Constructions.localLefschetzLaplacian, LocalLaplacianBoundary.Constructions.localLefschetzLaplacian,
    extDeriv_congr_of_eventuallyEq (n + 1) hB, ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_congr (n + 1) J K2 K1 hd]

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalLaplacianLocality.Constructions
