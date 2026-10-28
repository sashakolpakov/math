import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.JetExtraction
import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.FamilyGerms

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder

variable {Z E X P V ι : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance parameterRegularityFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance parameterRegularityFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance parameterRegularitySecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterRegularitySecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterRegularityHolderGroup {Ω K : Set E} (h : Ω ⊆ K) (α : ℝ) :
    NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) h α) := inferInstance
local instance parameterRegularityHolderSpace {Ω K : Set E} (h : Ω ⊆ K) (α : ℝ) :
    NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) h α) := inferInstance

/-- One common patch works simultaneously for every order and every
mixed tangential parameter direction. No shrinking with the order occurs. -/
theorem HasGeometricSolutionFamilies.all_mixed_tangent_orders
    {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r ψ B : E → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hc : ParameterDeformation.HasGeometricSolutionFamilies (Z := Z) e b r ψ B hΩD α)
    (hr : ContDiff ℝ 3 r) (hrp : LatticePeriodic e b r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (j : X ≃ₗᵢ[ℝ] E) (G : X → E) (P' : E → X)
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P')
    (hinv : (fun z ↦ P' (G z)) =ᶠ[𝓝 (0 : X)] id)
    (ℓ : X →L[ℝ] ℝ) (c : ℝ)
    (hlevel : ∀ z ∈ ball (0 : X) 1, r (G z) = c+ℓ z)
    (A : Z →L[ℝ] X) (hA : ∀ t, ℓ (A t) = 0)
    {S : Set X} (hGS : MapsTo G S {x | r x ≤ 0}) :
    ∃ O : Set X, IsOpen O ∧ (0 : X) ∈ O ∧
      ∀ (N : ℕ) (v : Fin N → Z), ContDiffOn ℝ 2
        (fun z ↦ iteratedFDeriv ℝ N
          (fun t : Z ↦ ψ (G (z+A t))-B (G (z+A t))) 0 v) (S ∩ O) := by
  obtain ⟨D,hD⟩ := ParameterDeformation.exists_boundary_periodicDomainDeformation j e b r hrp hG hP rfl
    hinv ℓ c hlevel A hA
  obtain ⟨U,hU,he⟩ := hc D
  obtain ⟨O,hO,hzero,hgerm⟩ := ParameterDeformation.translation_curve_germs hGS A he hD
  refine ⟨O,hO,hzero,?_⟩
  intro N v
  exact ParameterDeformation.mixed_tangent_contDiffOn_of_parameter_family (S := S ∩ O) (G := G)
    (f := fun z ↦ ψ (G z)-B (G z)) hr hreg hU
    (hG.of_le (by simp)).contDiffOn (fun z hz ↦ hGS hz.1) A hgerm N v

/-- Full spatial smoothness in the interior follows directly from the
multi-parameter translation identity. No elliptic bootstrap is needed here. -/
theorem HasGeometricSolutionFamilies.contDiffAt_interior
    {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r ψ B : E → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hc : ParameterDeformation.HasGeometricSolutionFamilies (Z := E) e b r ψ B hΩD α)
    (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hB : ContDiff ℝ ∞ B) {a : E} (ha : r a < 0) :
    ContDiffAt ℝ ∞ ψ a := by
  obtain ⟨D,hD⟩ := ParameterDeformation.exists_interior_periodicDomainDeformation e b r hr hrp ha
    (ContinuousLinearMap.id ℝ E)
  obtain ⟨U,hU,hvalue⟩ := hc D
  have hgerm : (fun t : E ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨a,ha.le⟩) =ᶠ[𝓝 0]
      (fun t ↦ ψ (a+t)-B (a+t)) := by
    have ht : Tendsto (fun t : E ↦ (t,a)) (𝓝 0) (𝓝 (0,a)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hvalue,ht.eventually hD] with t hv hd
    rw [hv ⟨a,ha.le⟩]
    change ψ (D.map (t,a))-B (D.map (t,a)) = _
    rw [hd]
    rfl
  let L : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α →L[ℝ] ℝ := jetValueEvaluation ⟨a,ha.le⟩
  have hs : ContDiffAt ℝ ∞ (fun t : E ↦ ψ (a+t)-B (a+t)) 0 :=
    (L.contDiff.contDiffAt.comp 0 hU).congr_of_eventuallyEq hgerm.symm
  have hsum : ContDiffAt ℝ ∞ (fun t : E ↦ ψ (a+t)) 0 := by
    have hb : ContDiffAt ℝ ∞ (fun t : E ↦ B (a+t)) 0 :=
      hB.contDiffAt.comp 0 (contDiffAt_const.add contDiffAt_id)
    simpa only [sub_add_cancel] using hs.add hb
  have hsuma : ContDiffAt ℝ ∞ (fun t : E ↦ ψ (a+t)) (a-a) := by
    simpa only [sub_self] using hsum
  have ht : ContDiffAt ℝ ∞ (fun x : E ↦ x-a) a := contDiffAt_id.sub contDiffAt_const
  convert hsuma.comp a (f := fun x : E ↦ x-a) ht using 1
  ext x
  congr 1
  simp only [← add_sub_assoc, add_sub_cancel_left]

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
