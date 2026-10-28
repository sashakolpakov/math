import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineFiberFlatness
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Relative Base Change -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.RelativeBaseChange.Construction

noncomputable section

section

/-! Flatness and localization at scheme stalks for Openness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

/-- The canonical morphism from the spectrum of a scheme stalk is flat. -/
theorem flat_fromSpecStalk (X : Scheme) (x : X) : Flat (X.fromSpecStalk x) := by
  let U := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hx : x ∈ U := X.affineCover.covers x
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    have := hU.isLocalization_stalk ⟨x, hx⟩
    apply Flat.SpecMap_iff.mpr
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

/-- Flatness of a composite can be cancelled across a monomorphism of
schemes, since the first map is a base change of the composite. -/
theorem flat_of_comp_mono
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] [Flat (f ≫ g)] : Flat f := by
  have heq : f = inv (pullback.fst (f ≫ g) g) ≫ pullback.snd (f ≫ g) g := by
    simp [← cancel_mono g, pullback.condition]
  rw [heq]
  infer_instance

/-- A family that is flat over a scheme stays flat when its structural
map factors through the spectrum of a stalk of that scheme. -/
theorem flat_of_comp_fromSpecStalk
    {X S : Scheme} (s : S) (f : X ⟶ Spec (S.presheaf.stalk s))
    [Flat (f ≫ S.fromSpecStalk s)] : Flat f :=
  flat_of_comp_mono f (S.fromSpecStalk s)

/-- Flatness can be tested after pulling back to the spectrum of every
target stalk. This form keeps finite morphisms finite under the test. -/
theorem flat_iff_flat_targetStalk_baseChange
    {X Y : Scheme} (f : X ⟶ Y) :
    Flat f ↔ ∀ y : Y, Flat (pullback.snd f (Y.fromSpecStalk y)) := by
  constructor
  · intro hf y
    have := hf
    infer_instance
  · intro hf
    apply Flat.of_stalkMap
    intro x
    let i := Y.fromSpecStalk (f x)
    let l := pullback.lift (X.fromSpecStalk x) (Spec.map (f.stalkMap x))
      (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm
    have : Flat (pullback.snd f i) := hf (f x)
    have : Flat (l ≫ pullback.fst f i) := by
      dsimp [l, i]
      rw [pullback.lift_fst]
      exact flat_fromSpecStalk X x
    have : Flat l := flat_of_comp_mono l (pullback.fst f i)
    have hcomp : Flat (l ≫ pullback.snd f i) := inferInstance
    have hmap : Flat (Spec.map (f.stalkMap x)) := by
      simpa only [l, i, pullback.lift_snd] using hcomp
    exact Flat.SpecMap_iff.mp hmap

end

/-! Relative base-change squares for the Openness fiberwise flatness argument. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

/-- Flatness of a structural morphism is invariant under an isomorphism over the base. -/
theorem flat_of_overIso {S : Scheme} {X Y : Over S} (e : X ≅ Y) [Flat Y.hom] :
    Flat X.hom := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  rw [← e.hom.w]
  infer_instance

/-- Either orientation of the same pullback gives the same flatness test. -/
theorem flat_pullback_fst_iff_snd
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) :
    Flat (pullback.fst f g) ↔ Flat (pullback.snd g f) := by
  constructor
  · intro h
    have := h
    rw [← pullbackSymmetry_inv_comp_fst f g]
    infer_instance
  · intro h
    have := h
    rw [← pullbackSymmetry_hom_comp_snd f g]
    infer_instance

/-- Successive target base changes preserve a flatness result obtained
for their composite. -/
theorem flat_iterated_targetBaseChange
    {X Y Z W : Scheme} (f : X ⟶ Y) (i : Z ⟶ Y) (j : W ⟶ Z)
    [Flat (pullback.snd f (j ≫ i))] : Flat (pullback.snd (pullback.snd f i) j) := by
  have : Flat ((Over.pullback (j ≫ i)).obj (Over.mk f)).hom :=
    inferInstanceAs (Flat (pullback.snd f (j ≫ i)))
  exact flat_of_overIso ((Over.pullbackComp j i).app (Over.mk f)).symm

/-- The map between two base-changed S-schemes is the base change of the
original map along the projection from the new target. -/
theorem isPullback_overPullback_map
    {S Z : Scheme} {X Y : Over S} (f : X ⟶ Y) (t : Z ⟶ S) :
    IsPullback (pullback.fst X.hom t) ((Over.pullback t).map f).left
      f.left (pullback.fst Y.hom t) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback Y.hom t)
  · simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w] using
      IsPullback.of_hasPullback X.hom t
  · simp only [Over.pullback_map_left, pullback.lift_fst]

/-- If the relative morphism is flat after changing the base to `Z`,
it is flat after any target base change whose map to S factors through Z. -/
theorem flat_targetBaseChange_of_factorization
    {S Z W : Scheme} {X Y : Over S} (f : X ⟶ Y) (t : Z ⟶ S)
    (u : W ⟶ Y.left) (v : W ⟶ Z) (h : u ≫ Y.hom = v ≫ t)
    [Flat ((Over.pullback t).map f).left] : Flat (pullback.snd f.left u) := by
  let l := pullback.lift u v h
  have hp := isPullback_overPullback_map f t
  have hq : IsPullback (pullback.fst f.left u) (pullback.snd f.left u)
      f.left (l ≫ pullback.fst Y.hom t) := by
    simpa only [l, pullback.lift_fst] using IsPullback.of_hasPullback f.left u
  exact MorphismProperty.of_isPullback (IsPullback.of_right' hq hp) inferInstance

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.RelativeBaseChange.Construction
