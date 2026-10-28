import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Invariant Affine Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.InvariantAffineCover

noncomputable section

/-! Reduction retains an actual invariant affine cover and the
endomorphisms of the original parameter, with their exact projection equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

def reducedEndomorphism {S : Scheme.{0}} {X : Over S} (a : X ⟶ X) : Reduction.reduction X ⟶ Reduction.reduction X :=
  Reduction.factorToReduction (Reduction.reductionι X ≫ a)

theorem reducedEndomorphism_ι {S : Scheme.{0}} {X : Over S} (a : X ⟶ X) :
    reducedEndomorphism a ≫ Reduction.reductionι X = Reduction.reductionι X ≫ a := Reduction.factorToReduction_ι _

theorem invariant_affine_cover_reduction {S : Scheme.{0}} (X : Over S) {I G : Type}
    (a : G → (X ⟶ X)) (V : I → X.left.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcover : iSup V = ⊤)
    (hInv : ∀ g i, (a g).left ⁻¹ᵁ V i = V i) :
    (∀ i, IsAffineOpen ((Reduction.reductionι X).left ⁻¹ᵁ V i)) ∧
      (⨆ i, (Reduction.reductionι X).left ⁻¹ᵁ V i) = ⊤ ∧
      (∀ g i, (reducedEndomorphism (a g)).left ⁻¹ᵁ ((Reduction.reductionι X).left ⁻¹ᵁ V i) =
        (Reduction.reductionι X).left ⁻¹ᵁ V i) := by
  refine ⟨fun i => (hV i).preimage (Reduction.reductionι X).left, ?_, ?_⟩
  · apply top_le_iff.mp
    intro x _
    have hx : (Reduction.reductionι X).left x ∈ iSup V := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro g i
    have he : (reducedEndomorphism (a g)).left ≫ (Reduction.reductionι X).left =
        (Reduction.reductionι X).left ≫ (a g).left := congrArg Over.Hom.left (reducedEndomorphism_ι (a g))
    rw [← Scheme.Hom.comp_preimage, he, Scheme.Hom.comp_preimage, hInv]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.InvariantAffineCover
