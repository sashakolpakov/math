import OAI.Analysis.PDE.Dirichlet.C2HolderImplicit
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! The parameter trick does not require continuity of the action on a
full Hölder space. Global uniqueness identifies an arbitrary candidate with
the smooth local implicit branch. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

section ParameterTrick

variable {P X Y : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- Smoothness of a uniquely determined candidate follows from parametric
IFT without assuming that the candidate is continuous in the Banach norm. -/
theorem contDiffAt_of_implicit_global_uniqueness
    (Q : P × X → Y) {a : P} {x : X} {q : ℕ∞ω}
    (hQ : ContDiffAt ℝ q Q (a, x)) (hq : q ≠ 0)
    (hderiv : ((fderiv ℝ Q (a, x)).comp (ContinuousLinearMap.inr ℝ P X)).IsInvertible)
    (c : P → X) {S : Set X} (hS : S ∈ 𝓝 x)
    (hunique : ∀ᶠ t in 𝓝 a, ∀ y ∈ S, Q (t, y) = Q (a, x) → y = c t) :
    ContDiffAt ℝ q c a := by
  let g : P → X := hQ.implicitFunction hq hderiv
  have hg : ContDiffAt ℝ q g a := hQ.contDiffAt_implicitFunction hq hderiv
  have hga : g a = x := hQ.implicitFunction_apply_self hq hderiv
  have hgS : ∀ᶠ t in 𝓝 a, g t ∈ S := by
    have ht : Tendsto g (𝓝 a) (𝓝 x) := by simpa only [hga] using hg.continuousAt.tendsto
    exact ht hS
  have he : c =ᶠ[𝓝 a] g := by
    filter_upwards [hunique, hgS, hQ.eventually_apply_implicitFunction hq hderiv]
      with t ht hgt hQt
    exact (ht (g t) hgt hQt).symm
  exact hg.congr_of_eventuallyEq he

end ParameterTrick

section Invertibility

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace Y] in
/-- Invertibility persists at nearby, potentially rough, Banach-space
solutions. No classical representative of a nearby point is needed. -/
theorem eventually_fderiv_isInvertible
    {F : X → Y} {x : X} (hF : ContDiffAt ℝ ∞ F x)
    (hL : (fderiv ℝ F x).IsInvertible) :
    ∀ᶠ y in 𝓝 x, (fderiv ℝ F y).IsInvertible := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ F) x := hF.fderiv_right (by simp)
  have hc : ContinuousAt (fderiv ℝ F) x := hd.continuousAt
  exact hc.tendsto.eventually hL.eventually_nhds

end Invertibility

end OAI.Analysis.PDE.Dirichlet
