import OAI.AlgebraicGeometry.ComplexMultiplication.CMFlatteningCenteredTransport
import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeNeighborhoodPullback

/-! # Transported Normal Coclass -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.TransportedNormalCoclass

noncomputable section

/-! # Dimension transport preserves the actual normal-projection coclass -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory OAI.AlgebraicTopology.Singular

theorem transportedNormalCoclass_eq
    {M : Type} [TopologicalSpace M] {m n p : ℕ} (hp : n = p)
    (e : OpenPartialHomeomorph M ((Fin m → ℂ) × (Fin n → ℂ))) (S W : Set M)
    (hr : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hr' : ∀ y ∈ (CMFlatteningCenteredTransport.transportFlatteningChart rfl hp e).source,
      y ∈ S ↔ (CMFlatteningCenteredTransport.transportFlatteningChart rfl hp e y).2 = 0)
    (hW : W ⊆ e.source) (hW' : W ⊆ (CMFlatteningCenteredTransport.transportFlatteningChart rfl hp e).source) :
    AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass (Fin m → ℂ) p (CMFlatteningCenteredTransport.transportFlatteningChart rfl hp e)
      S hr' W hW' = hp ▸ AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass (Fin m → ℂ) n e S hr W hW := by
  subst p
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.TransportedNormalCoclass
