import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Invariant Affine Cover Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.InvariantAffineCoverIso

noncomputable section

/-! Transport an actual invariant affine cover through a compatible
isomorphism of its ambient schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem invariant_affine_cover_of_iso {S : Scheme.{0}} {X Y : Over S} {I G : Type}
    (e : X ≅ Y) (a : G → (X ⟶ X)) (b : G → (Y ⟶ Y))
    (he : ∀ g, a g ≫ e.hom = e.hom ≫ b g)
    (V : I → Y.left.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hcover : iSup V = ⊤)
    (hInv : ∀ g i, (b g).left ⁻¹ᵁ V i = V i) :
    ∃ W : I → X.left.Opens, (∀ i, IsAffineOpen (W i)) ∧ iSup W = ⊤ ∧
      (∀ g i, (a g).left ⁻¹ᵁ W i = W i) := by
  have : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  refine ⟨fun i => e.hom.left ⁻¹ᵁ V i, fun i => (hV i).preimage_of_isIso e.hom.left, ?_, ?_⟩
  · apply top_le_iff.mp
    intro x _
    have hx : e.hom.left x ∈ iSup V := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro g i
    have h : (a g).left ≫ e.hom.left = e.hom.left ≫ (b g).left := congrArg Over.Hom.left (he g)
    rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage, hInv]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.InvariantAffineCoverIso
