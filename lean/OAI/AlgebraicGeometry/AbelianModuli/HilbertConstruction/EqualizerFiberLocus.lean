import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Equalizer Fiber Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualizerFiberLocus

noncomputable section

/-! The locus where a whole fiber lies in the scheme-theoretic equalizer of two maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S Y : Scheme.{u}}

def equalizerFiberLocus (p : X ⟶ S) (f g : X ⟶ Y) : Set S :=
  (p '' (Set.range (equalizer.ι f g))ᶜ)ᶜ

theorem mem_equalizerFiberLocus_iff (p : X ⟶ S) (f g : X ⟶ Y) (s : S) :
    s ∈ equalizerFiberLocus p f g ↔
      ∀ x : X, p x = s → x ∈ Set.range (equalizer.ι f g) := by
  constructor
  · intro hs x hx
    by_contra h
    exact hs ⟨x, h, hx⟩
  · intro hs ⟨x, hx, hxs⟩
    exact hx (hs x hxs)

theorem equalizerFiberLocus_map_eq (p : X ⟶ S) (f g : X ⟶ Y)
    (s : S) (hs : s ∈ equalizerFiberLocus p f g) (x : X) (hx : p x = s) : f x = g x := by
  obtain ⟨z, rfl⟩ := (mem_equalizerFiberLocus_iff p f g s).mp hs x hx
  exact congrArg (fun a : equalizer f g ⟶ Y => a z) (equalizer.condition f g)

theorem equalizerFiberLocus_isClosed (p : X ⟶ S) (hp : IsOpenMap p)
    (f g : X ⟶ Y) [Y.IsSeparated] : IsClosed (equalizerFiberLocus p f g) :=
  (hp _ (equalizer.ι f g).isClosedEmbedding.isClosed_range.isOpen_compl).isClosed_compl

theorem restrictionEq_le_equalizerFiberLocus (p : X ⟶ S) (f g : X ⟶ Y) (V : S.Opens)
    (h : (p ⁻¹ᵁ V).ι ≫ f = (p ⁻¹ᵁ V).ι ≫ g) :
    (V : Set S) ⊆ equalizerFiberLocus p f g := by
  intro s hs
  apply (mem_equalizerFiberLocus_iff p f g s).mpr
  intro x hx
  have hpx : p x ∈ V := hx.symm ▸ hs
  let z : (p ⁻¹ᵁ V).toScheme := ⟨x, hpx⟩
  refine ⟨equalizer.lift (p ⁻¹ᵁ V).ι h z, ?_⟩
  exact congrArg (fun a : (p ⁻¹ᵁ V).toScheme ⟶ X => a z) (equalizer.lift_ι _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EqualizerFiberLocus
