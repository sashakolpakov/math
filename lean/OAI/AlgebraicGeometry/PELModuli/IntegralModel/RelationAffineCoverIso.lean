import OAI.AlgebraicGeometry.PELModuli.IntegralModel.InvariantAffineCoverIso

/-! # Relation Affine Cover Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.RelationAffineCoverIso

noncomputable section

/-! Transport of relation-invariant affine covers through compatible
isomorphisms of the ambient schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem relation_invariant_affine_cover_of_iso {S : Scheme.{0}}
    {X Y Z W : Over S} {I : Type}
    (e : X ≅ Y) (d : Z ⟶ W) (a b : Z ⟶ X) (a' b' : W ⟶ Y)
    (ha : a ≫ e.hom = d ≫ a') (hb : b ≫ e.hom = d ≫ b')
    (V : I → Y.left.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hcover : iSup V = ⊤)
    (hInv : ∀ i, a'.left ⁻¹ᵁ V i = b'.left ⁻¹ᵁ V i) :
    ∃ U : I → X.left.Opens, (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ ∧
      (∀ i, a.left ⁻¹ᵁ U i = b.left ⁻¹ᵁ U i) := by
  have : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  refine ⟨fun i => e.hom.left ⁻¹ᵁ V i, fun i => (hV i).preimage_of_isIso e.hom.left, ?_, ?_⟩
  · apply top_le_iff.mp
    intro x _
    have hx : e.hom.left x ∈ iSup V := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    have ha' : a.left ≫ e.hom.left = d.left ≫ a'.left := congrArg Over.Hom.left ha
    have hb' : b.left ≫ e.hom.left = d.left ≫ b'.left := congrArg Over.Hom.left hb
    rw [← Scheme.Hom.comp_preimage, ha', Scheme.Hom.comp_preimage, hInv i,
      ← Scheme.Hom.comp_preimage, ← hb', Scheme.Hom.comp_preimage]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.RelationAffineCoverIso
