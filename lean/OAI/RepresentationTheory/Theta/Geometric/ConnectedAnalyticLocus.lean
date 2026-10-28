import OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq

/-! # Connected Analytic Locus -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConnectedAnalyticLocus

noncomputable section

/-! A locally analytic equality locus containing an open part fills a
connected open domain. The statement is relative to the original domain. -/

open Set

open OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility

theorem connected_local_equations_eq_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U S : Set E} (hc : IsPreconnected U)
    (hlocal : ∀ x ∈ U, Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility.HasLocalEquations S x)
    (hne : (U ∩ interior S).Nonempty) : U ⊆ S := by
  let : PreconnectedSpace U := Subtype.preconnectedSpace hc
  let T : Set U := {x | x.val ∈ interior S}
  have ho : IsOpen T := isOpen_interior.preimage continuous_subtype_val
  have hcl : IsClosed T := by
    apply isClosed_of_closure_subset
    intro x hx
    have hv : x.val ∈ closure (interior S) := by
      have h := image_closure_subset_closure_image continuous_subtype_val ⟨x, hx, rfl⟩
      exact closure_mono (by rintro _ ⟨y, hy, rfl⟩; exact hy) h
    exact Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility.mem_interior_of_local_equations (hlocal x.val x.property) hv
  have ht : T.Nonempty := by
    obtain ⟨x, hxU, hxS⟩ := hne
    exact ⟨⟨x, hxU⟩, hxS⟩
  have hall : T = univ := (isClopen_iff.mp ⟨hcl, ho⟩).resolve_left ht.ne_empty
  intro x hx
  have hm : (⟨x, hx⟩ : U) ∈ T := by rw [hall]; trivial
  exact interior_subset hm

end

end OAI.RepresentationTheory.Theta.Geometric.ConnectedAnalyticLocus
