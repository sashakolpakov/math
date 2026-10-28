import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GlobalFunctionDimension

/-! # Pointed Family Fiber Connectedness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedFamilyFiberConnectedness

noncomputable section

/-! A pointed proper smooth family is geometrically connected exactly when every residue-field fiber has a one-dimensional space of global functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def schemeSectionBaseChange {X S T : Scheme.{u}} (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 S)
    (c : T ⟶ S) : T ⟶ pullback p c :=
  pullback.lift (c ≫ x) (𝟙 T) (by rw [Category.assoc, hx]; simp)

theorem schemeSectionBaseChange_section {X S T : Scheme.{u}} (p : X ⟶ S) (x : S ⟶ X) (hx : x ≫ p = 𝟙 S)
    (c : T ⟶ S) : schemeSectionBaseChange p x hx c ≫ pullback.snd p c = 𝟙 T :=
  pullback.lift_snd _ _ _

theorem properSmoothPointed_geometricallyConnected_iff_fiber_dimension_one
    {X S : Scheme.{u}} (p : X ⟶ S) [IsProper p] [Smooth p] (x : S ⟶ X) (hx : x ≫ p = 𝟙 S) :
    GeometricallyConnected p ↔ ∀ s : S, Field.GlobalFunctionDimension.fieldGlobalFunctionDimension (p.fiberToSpecResidueField s) = 1 := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  apply forall_congr'
  intro s
  have hp : IsProper (pullback.snd p (S.fromSpecResidueField s)) :=
    (inferInstance : MorphismProperty.IsStableUnderBaseChange (@IsProper : MorphismProperty Scheme.{u})).of_isPullback
      (IsPullback.of_hasPullback p (S.fromSpecResidueField s)) (inferInstance : IsProper p)
  have hs : Smooth (pullback.snd p (S.fromSpecResidueField s)) :=
    smooth_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback p (S.fromSpecResidueField s)) (inferInstance : Smooth p)
  exact @Field.GlobalFunctionDimension.properSmoothPointed_geometricallyConnected_iff_dimension_one
    (S.residueField s) inferInstance (p.fiber s) (p.fiberToSpecResidueField s) hp hs
    (schemeSectionBaseChange p x hx (S.fromSpecResidueField s))
    (schemeSectionBaseChange_section p x hx (S.fromSpecResidueField s))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedFamilyFiberConnectedness
