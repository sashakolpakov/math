import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.FamilyGerms

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder

variable {Z T E X : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

omit [NormedSpace ℝ Z] in
/-- Uniform solution and flow identities give one fixed external/spatial
patch for differentiation of every mixed parameter order. -/
theorem mixed_translation_family_germs
    {Φ : T × E → E} {G : X → E} {Q : Set X} (hGQ : MapsTo G Q K)
    {f : Z × E → ℝ} {U : Z × T → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α}
    {p₀ : Z} {a : X} (A : T →L[ℝ] X)
    (hvalue : ∀ᶠ p in 𝓝 (p₀,(0:T)), ∀ x : K,
      OAI.Analysis.Normed.Function.Holder.C2Holder.value (U p) x = f (p.1,Φ (p.2,x)))
    (hflow : (fun p : T × X ↦ Φ (p.1,G p.2)) =ᶠ[𝓝 (0,a)]
      fun p ↦ G (p.2+A p.1)) :
    ∃ S : Set Z, IsOpen S ∧ p₀ ∈ S ∧
      ∃ O : Set X, IsOpen O ∧ a ∈ O ∧
        ∀ p ∈ S, ∀ x (hx : x ∈ Q ∩ O),
          (fun s : Z × T ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U ((p,0)+s)) ⟨G x,hGQ hx.1⟩)
            =ᶠ[𝓝 0] fun s ↦ f (p+s.1,G (x+A s.2)) := by
  rw [nhds_prod_eq] at hvalue
  obtain ⟨S₀,hS₀,V,hV,hSV⟩ := Filter.mem_prod_iff.mp hvalue
  obtain ⟨S,hSS₀,hS,hp₀⟩ := mem_nhds_iff.mp hS₀
  obtain ⟨O,hO,ha,hgerm⟩ := ParameterDeformation.exists_open_parameter_germ_slices hflow
  refine ⟨S,hS,hp₀,O,hO,ha,?_⟩
  intro p hp x hx
  have hnear : ∀ᶠ q in 𝓝 (p,(0:T)), ∀ y : K,
      OAI.Analysis.Normed.Function.Holder.C2Holder.value (U q) y = f (q.1,Φ (q.2,y)) := by
    rw [nhds_prod_eq]
    exact Filter.mem_prod_iff.mpr ⟨S,hS.mem_nhds hp,V,hV,
      fun q hq ↦ hSV ⟨hSS₀ hq.1,hq.2⟩⟩
  have ht : Tendsto (fun s : Z × T ↦ (p,0)+s) (𝓝 0) (𝓝 (p,(0:T))) := by
    have hc : Continuous (fun s : Z × T ↦ (p,0)+s) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : Z × T)
  have hf : ∀ᶠ s : Z × T in 𝓝 0, Φ (s.2,G x) = G (x+A s.2) :=
    (continuous_snd.tendsto (0 : Z × T)).eventually (hgerm x hx.2)
  filter_upwards [ht.eventually hnear,hf] with s hs hsflow
  have hv := hs ⟨G x,hGQ hx.1⟩
  simpa only [Prod.fst_add,Prod.snd_add,zero_add,hsflow] using hv

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
