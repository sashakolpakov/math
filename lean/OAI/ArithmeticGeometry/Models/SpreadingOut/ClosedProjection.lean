import OAI.ArithmeticGeometry.Models.SpreadingOut.Graph

/-! # Closed Projection -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedProjection.Construction

noncomputable section

/-! A closed graph whose first coordinate is recovered from a closed affine
chart projects by a closed immersion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem closed_projection_of_chart_factor
    {S : Scheme.{u}} {Z X P U A : Over S}
    (p : Z ⟶ X) (q : Z ⟶ P)
    [IsClosedImmersion (pullback.lift p.left q.left (p.w.trans q.w.symm))]
    (j : U ⟶ X) (e : U ⟶ A) [IsClosedImmersion e.left]
    (r : P ⟶ A) (l : Z ⟶ U)
    (hp : l.left ≫ j.left = p.left)
    (he : l.left ≫ e.left = q.left ≫ r.left) : IsClosedImmersion q.left := by
  let C := pullback e.left r.left
  let k : Z.left ⟶ C := pullback.lift l.left q.left he
  have hv : (pullback.fst e.left r.left ≫ j.left) ≫ X.hom =
      pullback.snd e.left r.left ≫ P.hom := by
    rw [Category.assoc, j.w, ← e.w, ← Category.assoc, pullback.condition,
      Category.assoc, r.w]
  let v : C ⟶ pullback X.hom P.hom :=
    pullback.lift (pullback.fst e.left r.left ≫ j.left)
      (pullback.snd e.left r.left) hv
  have hvp : v ≫ pullback.snd X.hom P.hom = pullback.snd e.left r.left :=
    pullback.lift_snd _ _ _
  have hvx : v ≫ pullback.fst X.hom P.hom = pullback.fst e.left r.left ≫ j.left :=
    pullback.lift_fst _ _ _
  have : IsSeparated (v ≫ pullback.snd X.hom P.hom) := by
    rw [hvp]
    infer_instance
  have : IsSeparated v := IsSeparated.of_comp v (pullback.snd X.hom P.hom)
  have hkv : k ≫ v = pullback.lift p.left q.left (p.w.trans q.w.symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hvx, ← Category.assoc, pullback.lift_fst,
        hp, pullback.lift_fst]
    · rw [Category.assoc, hvp, pullback.lift_snd, pullback.lift_snd]
  have : IsClosedImmersion (k ≫ v) := by rw [hkv]; infer_instance
  have : IsClosedImmersion k := Graph.Construction.closed_immersion_of_comp_of_separated k v
  have hc : IsClosedImmersion (k ≫ pullback.snd e.left r.left) := inferInstance
  rwa [pullback.lift_snd] at hc

/-- Local closed embeddings on target charts that cover the image combine
to a global closed embedding when the map is proper. -/
theorem proper_closedImmersion_of_target_charts
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {ι : Type*} (U : ι → Y.Opens)
    (hcover : Set.range f ⊆ (⨆ i, U i : Y.Opens))
    (hclosed : ∀ i, IsClosedImmersion (f ∣_ U i)) : IsClosedImmersion f := by
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg ↦ by have := hi; have := hg; infer_instance⟩
  have : IsImmersion f := IsZariskiLocalAtTarget.of_range_subset_iSup
    (P := @IsImmersion) U hcover (fun i ↦ by have := hclosed i; infer_instance)
  exact IsClosedImmersion.of_isPreimmersion f f.isClosedMap.isClosed_range

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedProjection.Construction
