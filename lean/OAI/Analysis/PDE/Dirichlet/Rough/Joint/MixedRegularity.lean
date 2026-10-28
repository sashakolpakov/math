import OAI.Analysis.PDE.Dirichlet.Rough.Joint.BoundaryExtraction
import OAI.Analysis.PDE.Dirichlet.Rough.Joint.FamilyGerms

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder

variable {Z T E X : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [Nontrivial E] in
/-- One common external-parameter and spatial patch supports every mixed
tangential derivative extracted from the combined implicit family. -/
theorem all_joint_mixed_tangent_orders
    {r : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hr : ContDiff ℝ 3 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {Φ : T × E → E} {G : X → E} {Q : Set X}
    (hG : ContDiffOn ℝ 2 G Q) (hGQ : MapsTo G Q {x | r x ≤ 0})
    {f : Z × E → ℝ} {U : Z × T → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α}
    {W : Set (Z × T)} (hW : IsOpen W) (hU : ContDiffOn ℝ ∞ U W)
    {p₀ : Z} {a : X} (hp₀ : (p₀,(0:T)) ∈ W) (A : T →L[ℝ] X)
    (hvalue : ∀ᶠ p in 𝓝 (p₀,(0:T)), ∀ x : {x | r x ≤ 0},
      OAI.Analysis.Normed.Function.Holder.C2Holder.value (U p) x = f (p.1,Φ (p.2,x)))
    (hflow : (fun p : T × X ↦ Φ (p.1,G p.2)) =ᶠ[𝓝 (0,a)]
      fun p ↦ G (p.2+A p.1)) :
    ∃ S : Set Z, IsOpen S ∧ p₀ ∈ S ∧
      ∃ O : Set X, IsOpen O ∧ a ∈ O ∧
        ∀ (N : ℕ) (v : Fin N → Z × T), ContDiffOn ℝ 2
          (fun p : Z × X ↦ iteratedFDeriv ℝ N
            (fun s : Z × T ↦ f (p.1+s.1,G (p.2+A s.2))) 0 v) (S ×ˢ (Q ∩ O)) := by
  obtain ⟨S₀,hS₀,hpS₀,O,hO,ha,hgerm⟩ := ParameterDeformation.mixed_translation_family_germs hGQ A hvalue hflow
  let S : Set Z := S₀ ∩ (fun p : Z ↦ (p,(0:T))) ⁻¹' W
  have hS : IsOpen S := hS₀.inter (hW.preimage (continuous_id.prodMk continuous_const))
  refine ⟨S,hS,⟨hpS₀,hp₀⟩,O,hO,ha,?_⟩
  intro N v
  exact ParameterDeformation.contDiffOn_mixed_closed_chart_parameter hS hW (fun _ hp ↦ hp.2) hr hreg U hU
    G (hG.mono inter_subset_left) (fun _ hx ↦ hGQ hx.1)
    (fun p : Z × X ↦ f (p.1,G p.2)) A
    (fun p hp x hx ↦ hgerm p hp.1 x hx) N v

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
