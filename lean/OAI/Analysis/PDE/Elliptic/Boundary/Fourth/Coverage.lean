import OAI.Analysis.PDE.Elliptic.Boundary.InverseSubtractedFourth
import OAI.Analysis.PDE.Elliptic.Boundary.Third.Coverage

noncomputable section
open Set Filter Metric
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I
local instance fourthCover1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthCover1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthCover2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthCover2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthCover3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthCover3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [DecidableEq I] in
/-- A fixed physical neighborhood inherits the fourth-order Hölder bound
from the flat half-patch. The radius and constant are independent of u. -/
theorem exists_physical_fourth_return {P G : E → E} {a : E}
    {r ℓ : E → ℝ} {c : ℝ} (hc : 0 < c) (hr : Continuous r)
    (hP : ContDiff ℝ 5 P) (hG : ContDiff ℝ 5 G) (hG0 : G 0 = a)
    (hinv : (fun z => P (G z)) =ᶠ[𝓝 (0 : E)] id)
    (hlevel : ∀ z ∈ closedBall 0 2, r (G z)-r a = -c*ℓ z)
    (hra : r a = 0) (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 5 B₀)
    {α δ : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) :
    ∃ R > 0, ∃ C > 0, ∀ u : E → ℝ, ContDiff ℝ 4 u →
      ∀ N M : ℝ, 0 ≤ N → 0 ≤ M →
      OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn (fun z => u (G z)-B₀ (G z))
        (ball 0 δ ∩ {z | 0 ≤ ℓ z}) α N →
      (∀ z ∈ ball 0 δ ∩ {z | 0 ≤ ℓ z},
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y)-B₀ (G y)))) z‖ ≤ N) →
      (∀ z ∈ ball 0 δ ∩ {z | 0 ≤ ℓ z}, ∀ w ∈ ball 0 δ ∩ {z | 0 ≤ ℓ z},
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y)-B₀ (G y)))) z-
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y)-B₀ (G y)))) w‖ ≤ N*‖z-w‖^α) →
      HasFourthHolderBound (ball 0 δ ∩ {z | 0 ≤ ℓ z}) α (fun z => u (G z)-B₀ (G z)) M →
      HasFourthHolderBound (closedBall a R ∩ {x | r x ≤ 0}) α u (C*(1+N+M)) := by
  obtain ⟨R,hR,V,hV,_,hRV,hleft,hmaps⟩ := exists_level_chart_coverage hc
    (hP.of_le (by norm_num)) (hG.of_le (by norm_num)) hG0 hinv hlevel hra hδ
  have hcompact : IsCompact (closedBall a R ∩ {x | r x ≤ 0}) :=
    (isCompact_closedBall a R).inter_right (isClosed_le hr continuous_const)
  obtain ⟨C,hC,hreturn⟩ := exists_inverse_subtracted_fourth_holder hcompact hP B₀ hB₀ hα hα1
  refine ⟨R,hR,C,hC,?_⟩
  intro u hu N M hN hM hb hn hh hf
  have heq (x) (hx : x ∈ closedBall a R ∩ {x | r x ≤ 0}) :
      (fun y => u (G (P y))-B₀ (G (P y))) =ᶠ[𝓝 x] (fun y => u y-B₀ y) := by
    filter_upwards [hV.mem_nhds (hRV hx.1)] with y hy
    rw [hleft y hy]
  exact hreturn _ hmaps _ u
    ((hu.sub (hB₀.of_le (by norm_num))).comp (hG.of_le (by norm_num)))
    hu heq N M hN hM hb hn hh hf

end OAI.Analysis.PDE.Elliptic
