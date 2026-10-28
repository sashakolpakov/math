import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.ChartJets
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.ComposeTensor
import OAI.Analysis.PDE.Elliptic.Boundary.InverseThirdHolder
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Pullback
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.ChartBounds

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I

local instance inverseFourthScalar1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance inverseFourthScalar1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance inverseFourthScalar2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseFourthScalar2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseFourthScalar3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseFourthScalar3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseFourthScalar4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseFourthScalar4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseFourthMap1Group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance inverseFourthMap1Space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance inverseFourthMap2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance inverseFourthMap2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance inverseFourthMap3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance inverseFourthMap3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance inverseFourthMap4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance inverseFourthMap4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

omit [DecidableEq I] in
/-- Return the full fourth derivative from a fixed smooth chart. The
constant is chosen before the solution, and depends linearly on its lower
jet and fourth-derivative bounds. -/
theorem exists_inverse_chart_fourth_holder {S : Set E} (hS : IsCompact S)
    {P : E → E} (hP : ContDiff ℝ 5 P) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ K : Set E, MapsTo P S K → ∀ v u : E → ℝ, ContDiff ℝ 4 v →
      (∀ x ∈ S, (fun y => v (P y)) =ᶠ[𝓝 x] u) →
      ∀ N M : ℝ, 0 ≤ N → 0 ≤ M → OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn v K α N →
      (∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ ≤ N) →
      (∀ x ∈ K, ∀ y ∈ K,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ v)) y‖ ≤
          N*‖x-y‖^α) →
      HasFourthHolderBound K α v M → HasFourthHolderBound S α u (C*(N+M)) := by
  obtain ⟨A,hA,J,J₂,J₃,J₄,hJ,hJ₂,hJ₃,hJ₄,hJn,hJ₂n,hJ₃n,hJ₄n⟩ :=
    exists_bounded_fourth_chart_jets hS hP hα hα1
  obtain ⟨L,hL,_,hLip⟩ := OAI.Analysis.PDE.Dirichlet.smooth_jet_compact_holder_bound P (hP.of_le (by norm_num))
    hS (by norm_num : (0 : ℝ) ≤ 1) le_rfl
  let B := max 1 (L^α)
  have hB : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  let C := (Fintype.card I : ℝ)^4*15*(2*A)^4*B+1
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro K hPK v u hv heq N M hN hM hvb hvn hvh hvfour
  have hpl (x y : S) : dist (P x) (P y) ≤ L*dist x y := by
    simpa only [Subtype.dist_eq,dist_eq_norm,Real.rpow_one] using hLip x x.property y y.property
  have hc := exists_fourth_holder_of_chart_jets hα hA hL.le (hP.of_le (by norm_num))
    hPK hpl J J₂ J₃ J₄ hJ hJ₂ hJ₃ hJ₄
    hJn hJ₂n hJ₃n hJ₄n
    v hv hN hM hvb hvn hvh hvfour
  have hc' : HasFourthHolderBound S α (fun y => v (P y)) (C*(N+M)) := hc.mono (by
    calc
      _ = (C-1)*(N+M) := by dsimp only [C]; ring
      _ ≤ C*(N+M) := mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hN hM))
  obtain ⟨U,hU,hUn⟩ := hc'
  refine ⟨U,?_,hUn⟩
  intro x
  exact (hU x).trans ((((heq x x.property).fderiv.fderiv).fderiv).fderiv_eq)

end OAI.Analysis.PDE.Elliptic
