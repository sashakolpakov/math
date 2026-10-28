import OAI.AlgebraicGeometry.PELModuli.IntegralModel.MaximalFiniteOpen
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteTargetFibers

/-! # Relative Finite Neighborhood -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.RelativeFiniteNeighborhood

noncomputable section

/-! For a proper target family, finiteness of one coefficient fiber
extends to an open base neighborhood, with arbitrary further base change. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ B) [IsProper q]

def properRelativeFiniteOpen : B.Opens :=
  ⟨(q '' (MaximalFiniteOpen.maximalFiniteOpen f : Set Y)ᶜ)ᶜ,
    (q.isClosedMap _ (MaximalFiniteOpen.maximalFiniteOpen f).isOpen.isClosed_compl).isOpen_compl⟩

theorem mem_properRelativeFiniteOpen (b : B) :
    b ∈ properRelativeFiniteOpen f q ↔ ∀ y : Y, q y = b → y ∈ MaximalFiniteOpen.maximalFiniteOpen f := by
  constructor
  · intro h y hy
    by_contra hn
    exact h ⟨y, hn, hy⟩
  · intro h
    rintro ⟨y, hy, he⟩
    exact hy (h y he)

theorem mem_properRelativeFiniteOpen_of_finite_fiber [IsProper f] (b : B)
    (h : IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField b))) :
    b ∈ properRelativeFiniteOpen f q := by
  apply (mem_properRelativeFiniteOpen f q b).mpr
  intro y hy
  subst b
  apply (MaximalFiniteOpen.mem_maximalFiniteOpen f y).mpr
  apply Relative.FiniteTargetFibers.exists_finite_target_neighborhood_of_relative_finite f q y
  exact h

theorem relativeMorphismBaseChange_isFinite_of_range_subset {T : Scheme.{u}}
    (g : T ⟶ B) (h : Set.range g ⊆ (properRelativeFiniteOpen f q : Set B)) :
    IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g) := by
  rw [Finite.PullbackTransport.relativeMorphismBaseChange_isFinite_iff, Finite.PullbackTransport.finite_pullback_snd_iff_fst]
  let := MaximalFiniteOpen.maximalFiniteOpen_restrict_isFinite f
  apply Finite.PullbackTransport.finite_pullback_fst_of_range_subset_open f (MaximalFiniteOpen.maximalFiniteOpen f)
  rw [Scheme.Pullback.range_fst]
  rintro y ⟨t, ht⟩
  exact (mem_properRelativeFiniteOpen f q (g t)).mp (h ⟨t, rfl⟩) y ht.symm

theorem properRelativeFiniteOpen_baseChange_isFinite :
    IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q (properRelativeFiniteOpen f q).ι) := by
  apply relativeMorphismBaseChange_isFinite_of_range_subset f q
  rw [Scheme.Opens.range_ι]

theorem exists_finite_base_neighborhood_of_finite_fiber [IsProper f] (b : B)
    (h : IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField b))) :
    ∃ U : B.Opens, b ∈ U ∧ IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q U.ι) :=
  ⟨properRelativeFiniteOpen f q,
    mem_properRelativeFiniteOpen_of_finite_fiber f q b h,
    properRelativeFiniteOpen_baseChange_isFinite f q⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.RelativeFiniteNeighborhood
