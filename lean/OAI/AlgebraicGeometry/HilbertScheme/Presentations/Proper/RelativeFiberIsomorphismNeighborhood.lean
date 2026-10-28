import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.IsomorphismTargetFibers
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.TargetRestrictionIsomorphism
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FiberIsomorphismAtTarget
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.StalkIsomorphismNeighborhood
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MaximalIsomorphismOpen

/-! # Relative Fiber Isomorphism Neighborhood -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeFiberIsomorphismNeighborhood

noncomputable section

/-! For a proper family morphism with parameter-flat source, an
isomorphic coefficient fiber gives an isomorphism neighborhood at every target point in it. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B : Scheme.{u}} [IsLocallyNoetherian Y]
variable (f : X ⟶ Y) (q : Y ⟶ B) [IsProper f] [Flat (f ≫ q)]

theorem exists_isomorphism_neighborhood_of_relative_fiber (y : Y)
    (h : IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField (q y)))) :
    ∃ W : Y.Opens, y ∈ W ∧ IsIso (f ∣_ W) := by
  obtain ⟨U, hy, hfin⟩ := Relative.IsomorphismTargetFibers.exists_finite_target_neighborhood_of_relative_isomorphism f q y h
  let := hfin
  let u : U.toScheme := ⟨y, hy⟩
  let q' := U.ι ≫ q
  have hflat : Flat ((f ∣_ U) ≫ q') := by
    change Flat ((f ∣_ U) ≫ U.ι ≫ q)
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  let := hflat
  have hu : IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange (f ∣_ U) q'
      (B.fromSpecResidueField (q' u))) :=
    Relative.TargetRestrictionIsomorphism.relativeMorphismBaseChange_restrict_target f q U (B.fromSpecResidueField (q y)) h
  have hi := Finite.FiberIsomorphismAtTarget.finite_isIso_at_target_of_fiber (f ∣_ U) q' u hu
  obtain ⟨V, hv, hV⟩ := Finite.StalkIsomorphismNeighborhood.exists_open_finite_isomorphism_of_stalk (f ∣_ U) u hi
  refine ⟨U.ι ''ᵁ V, ⟨u, hv, rfl⟩, ?_⟩
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictRestrict f U V)).mp hV

theorem mem_maximalIsomorphismOpen_of_relative_fiber (y : Y)
    (h : IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField (q y)))) :
    y ∈ MaximalIsomorphismOpen.maximalIsomorphismOpen f :=
  (MaximalIsomorphismOpen.mem_maximalIsomorphismOpen f y).mpr
    (exists_isomorphism_neighborhood_of_relative_fiber f q y h)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeFiberIsomorphismNeighborhood
