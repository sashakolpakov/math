import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeFiberIsomorphismNeighborhood
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OnOpenBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Relative Isomorphism Open -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeIsomorphismOpen

noncomputable section

/-! For a proper morphism with parameter-flat source and proper target,
the parameters with isomorphic fibers form an actual open subscheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B : Scheme.{u}}
variable (f : X ⟶ Y) (q : Y ⟶ B) [IsProper q]

def properRelativeIsomorphismOpen : B.Opens :=
  ⟨(q '' (MaximalIsomorphismOpen.maximalIsomorphismOpen f : Set Y)ᶜ)ᶜ,
    (q.isClosedMap _ (MaximalIsomorphismOpen.maximalIsomorphismOpen f).isOpen.isClosed_compl).isOpen_compl⟩

theorem mem_properRelativeIsomorphismOpen (b : B) :
    b ∈ properRelativeIsomorphismOpen f q ↔
      ∀ y : Y, q y = b → y ∈ MaximalIsomorphismOpen.maximalIsomorphismOpen f := by
  constructor
  · intro h y hy
    by_contra hn
    exact h ⟨y, hn, hy⟩
  · intro h
    rintro ⟨y, hy, he⟩
    exact hy (h y he)

theorem properRelativeIsomorphismOpen_fiber_iff
    [IsLocallyNoetherian Y] [IsProper f] [Flat (f ≫ q)] (b : B) :
    b ∈ properRelativeIsomorphismOpen f q ↔
      IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField b)) := by
  constructor
  · intro h
    rw [Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange_isIso_iff, Relative.SourceIsomorphismTransport.isIso_pullback_snd_iff_fst]
    let := MaximalIsomorphismOpen.maximalIsomorphismOpen_restrict_isIso f
    apply OnOpenBaseChange.isIso_pullback_fst_of_range_subset_isomorphism_open f
      (MaximalIsomorphismOpen.maximalIsomorphismOpen f)
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
    intro y hy
    exact (mem_properRelativeIsomorphismOpen f q b).mp h y hy
  · intro h
    apply (mem_properRelativeIsomorphismOpen f q b).mpr
    intro y hy
    apply RelativeFiberIsomorphismNeighborhood.mem_maximalIsomorphismOpen_of_relative_fiber f q y
    rw [hy]
    exact h

theorem properRelativeIsomorphismOpen_isIso_of_range
    {T : Scheme.{u}} (g : T ⟶ B)
    (h : Set.range g ⊆ (properRelativeIsomorphismOpen f q : Set B)) :
    IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g) := by
  rw [Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange_isIso_iff, Relative.SourceIsomorphismTransport.isIso_pullback_snd_iff_fst]
  let := MaximalIsomorphismOpen.maximalIsomorphismOpen_restrict_isIso f
  apply OnOpenBaseChange.isIso_pullback_fst_of_range_subset_isomorphism_open f
    (MaximalIsomorphismOpen.maximalIsomorphismOpen f)
  rw [Scheme.Pullback.range_fst]
  intro y hy
  exact (mem_properRelativeIsomorphismOpen f q (q y)).mp (h hy) y rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeIsomorphismOpen
