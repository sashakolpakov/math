import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.ComposeTensor
import OAI.Analysis.PDE.Elliptic.Boundary.InverseThirdHolder

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

@[instance_reducible]
private def fourthPullHolderNorm (X F : Type*) [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) : Norm (OAI.Analysis.Normed.Function.Holder.HolderMap X F α) := inferInstance

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I

local instance fourthPull1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthPull1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthPull2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthPull2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthPull3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthPull3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthPull4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthPull4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthPullMap1Group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance fourthPullMap1Space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance fourthPullMap2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthPullMap2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthPullMap3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthPullMap3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthPullMap4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthPullMap4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthPullMap4Norm {S : Set E} {α : ℝ} :
    Norm (OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α) := fourthPullHolderNorm _ _ α

omit [DecidableEq I] in
theorem exists_fourth_holder_of_chart_jets
    {S K : Set E} {α A L : ℝ} (hα : 0 ≤ α) (hA : 1 ≤ A) (hL : 0 ≤ L)
    {P : E → E} (hP : ContDiff ℝ 4 P) (hPK : MapsTo P S K)
    (hpl : ∀ x y : S, dist (P x) (P y) ≤ L*dist x y)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
    (J₂ : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
    (J₃ : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (J₄ : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (hJ : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ P x)
    (hJ₂ : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J₂ x = fderiv ℝ (fderiv ℝ P) x)
    (hJ₃ : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J₃ x = fderiv ℝ (fderiv ℝ (fderiv ℝ P)) x)
    (hJ₄ : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J₄ x = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ P))) x)
    (hJn : ‖J‖ ≤ A) (hJ₂n : ‖J₂‖ ≤ A) (hJ₃n : ‖J₃‖ ≤ A) (hJ₄n : ‖J₄‖ ≤ A)
    (v : E → ℝ) (hv : ContDiff ℝ 4 v) {N M : ℝ} (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hvb : OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn v K α N)
    (hvn : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ ≤ N)
    (hvh : ∀ x ∈ K, ∀ y ∈ K,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ v)) y‖ ≤ N*‖x-y‖^α)
    (hvfour : HasFourthHolderBound K α v M) :
    HasFourthHolderBound S α (fun y => v (P y))
      ((Fintype.card I : ℝ)^4*(15*((2*A)^4*(max 1 (L^α)*(N+M))))) := by
  let B := max 1 (L^α)
  have hB : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  let p : S → K := fun x => ⟨P x,hPK x.property⟩
  have hp : Continuous p := (hP.continuous.comp continuous_subtype_val).subtype_mk _
  obtain ⟨D',H',T',hD',hH',hT',hD'n,hH'n,hT'n⟩ :=
    exists_pulledback_jet_holders hα hL hN hN p hp hpl v (hv.of_le (by norm_num)) hvb hvn hvh
  obtain ⟨Q,hQ,hQn⟩ := hvfour
  obtain ⟨Q',hQ',hQ'n⟩ := OAI.Analysis.Normed.Function.Holder.exists_holder_lipschitz_pullback hα Q p hp hL hpl
  have hNlarge : B*N ≤ B*(N+M) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hM) hB
  have hMlarge : B*M ≤ B*(N+M) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hN) hB
  have hqval (x : S) : OAI.Analysis.Normed.Function.Holder.HolderMap.value Q' x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ v))) (P x) := (hQ' x).trans (hQ (p x))
  have hqnorm : ‖Q'‖ ≤ B*(N+M) :=
    hQ'n.trans ((mul_le_mul_of_nonneg_left hQn hB).trans hMlarge)
  exact exists_composed_fourth_holder (EuclideanSpace.basisFun I ℝ) hα hv hP
    D' H' T' Q' J J₂ J₃ J₄ hD' hH' hT' hqval hJ hJ₂ hJ₃ hJ₄
    (mul_nonneg hB (add_nonneg hN hM)) hA
    (hD'n.trans hNlarge) (hH'n.trans hNlarge) (hT'n.trans hNlarge) hqnorm hJn hJ₂n hJ₃n hJ₄n

end OAI.Analysis.PDE.Elliptic
