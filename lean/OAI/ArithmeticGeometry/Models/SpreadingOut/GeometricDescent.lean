import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents

/-! # Geometric Descent -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricDescent.Construction

noncomputable section

/-! Descent of geometric properties detected by surjective morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem geometrically_of_surjective_baseChange
    (P : ObjectProperty Scheme.{u}) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ {A B : Scheme.{u}} (a : A ⟶ B), Surjective a → P A → P B)
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) [Surjective g]
    (hf : geometrically P (pullback.snd f g)) : geometrically P f := by
  classical
  refine geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_
  let W : Scheme.{u} := pullback g y
  have : Surjective (pullback.snd g y) := inferInstance
  obtain ⟨w, -⟩ := (pullback.snd g y).surjective (Classical.choice inferInstance)
  let T := W.residueField w
  let a : Spec T ⟶ Y' := W.fromSpecResidueField w ≫ pullback.fst g y
  let b : Spec T ⟶ Spec (.of K) := W.fromSpecResidueField w ≫ pullback.snd g y
  have hab : a ≫ g = b ≫ y := by simp [a, b, pullback.condition]
  let Z : Scheme.{u} := pullback (pullback.snd f y) b
  let p : Z ⟶ pullback f g := pullback.lift
    (pullback.fst _ b ≫ pullback.fst f y) (pullback.snd _ b ≫ a) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, ← hab]
      exact (Category.assoc _ _ _).symm)
  have houter : IsPullback (p ≫ pullback.fst f g) (pullback.snd _ b) f (a ≫ g) := by
    simpa only [p, pullback.lift_fst, hab] using
      (IsPullback.of_hasPullback (pullback.snd f y) b).paste_horiz
        (IsPullback.of_hasPullback f y)
  have hp : IsPullback p (pullback.snd _ b) (pullback.snd f g) a :=
    IsPullback.of_right houter (by simp only [p, pullback.lift_snd]) (IsPullback.of_hasPullback f g)
  have hZ : P Z := hf a p (pullback.snd _ b) hp
  exact hP (pullback.fst (pullback.snd f y) b) inferInstance hZ

theorem geometricallyConnected_of_surjective_baseChange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) [Surjective g]
    [GeometricallyConnected (pullback.snd f g)] : GeometricallyConnected f := by
  refine ⟨geometrically_of_surjective_baseChange (ConnectedSpace ·) ?_ f g
    GeometricallyConnected.geometrically_connectedSpace⟩
  intro A B a ha hA
  have : Surjective a := ha
  have : ConnectedSpace A := hA
  exact a.surjective.connectedSpace a.continuous

theorem geometricallyIrreducible_of_surjective_baseChange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) [Surjective g]
    [GeometricallyIrreducible (pullback.snd f g)] : GeometricallyIrreducible f := by
  refine ⟨geometrically_of_surjective_baseChange (IrreducibleSpace ·) ?_ f g
    GeometricallyIrreducible.geometrically_irreducibleSpace⟩
  intro A B a ha hA
  have : Surjective a := ha
  have : IrreducibleSpace A := hA
  exact GeometricFieldComponents.Construction.irreducibleSpace_of_dominant a

theorem geometricallyConnected_of_surjective_cartesian
    {W X Y Z : Scheme.{u}} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p q f g) [Surjective g] [GeometricallyConnected q] :
    GeometricallyConnected f := by
  have : GeometricallyConnected (pullback.snd f g) := by
    refine ⟨fun L _ y A p' q' hp ↦ ?_⟩
    have hp' : IsPullback (p' ≫ h.isoPullback.inv) q' q y := by
      apply hp.of_iso (Iso.refl _) h.isoPullback.symm (Iso.refl _) (Iso.refl _)
      · simp
      · simp
      · simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
          h.isoPullback_inv_snd.symm
      · simp
    exact GeometricallyConnected.geometrically_connectedSpace y _ _ hp'
  exact geometricallyConnected_of_surjective_baseChange f g

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricDescent.Construction
