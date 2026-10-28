import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Connected.Clopen

/-! # Functions Connectedness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsConnectedness

noncomputable section

/-! A scheme whose ring of global functions is a domain is preconnected: a nontrivial clopen decomposition would split that ring as a product of two nonzero rings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem scheme_preconnected_of_globalSections_domain (X : Scheme.{u}) [IsDomain Γ(X, ⊤)] :
    PreconnectedSpace X := by
  classical
  apply preconnectedSpace_iff_clopen.mpr
  intro s hs
  by_cases he : s = ∅
  · exact Or.inl he
  · right
    by_contra ht
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr he
    have hc : ∃ y : X, y ∉ s := by
      by_contra! h
      exact ht (Set.eq_univ_of_forall h)
    obtain ⟨y, hy⟩ := hc
    let U : X.Opens := ⟨s, hs.isOpen⟩
    let V : X.Opens := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    have : Nonempty V := ⟨⟨y, hy⟩⟩
    have hdis : U ⊓ V = ⊥ := by
      ext z
      change (z ∈ s ∧ z ∉ s) ↔ False
      exact iff_false_intro (fun h => h.2 h.1)
    have hsup : U ⊔ V = ⊤ := by
      ext z
      change (z ∈ s ∨ z ∉ s) ↔ True
      exact iff_true_intro (em (z ∈ s))
    have : IsDomain Γ(X, U ⊔ V) := by rw [hsup]; infer_instance
    let e : Γ(X, U ⊔ V) ≅ CommRingCat.of (Γ(X, U) × Γ(X, V)) :=
      (X.sheaf.isProductOfDisjoint U V hdis).conePointUniqueUpToIso (CommRingCat.prodFanIsLimit _ _)
    have : IsDomain (Γ(X, U) × Γ(X, V)) := e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    exact false_of_nontrivial_of_product_domain Γ(X, U) Γ(X, V)

theorem scheme_connected_of_globalSections_domain (X : Scheme.{u}) [Nonempty X] [IsDomain Γ(X, ⊤)] :
    ConnectedSpace X := by
  let : PreconnectedSpace X := scheme_preconnected_of_globalSections_domain X
  exact ⟨inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsConnectedness
