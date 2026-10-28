import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothReducedOf
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Scheme Smooth -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced

/-!
# Reduced fibers of smooth schemes and finite flat quotients
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- A scheme smooth over a field is reduced. -/
theorem reduced_of_smooth_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] : IsReduced X := by
  apply (IsReduced.iff_of_openCover X X.affineCover).mpr
  intro i
  let g := X.affineCover.f i ≫ f
  let := g.appTop.hom.toAlgebra
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  have : Algebra.Smooth Γ(Spec (.of K), ⊤) Γ(X.affineCover.X i, ⊤) :=
    HasRingHomProperty.appTop (P := @Smooth) g inferInstance
  have : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
    SmoothReducedOf.Construction.SmoothReduced.of_smooth_field (K := Γ(Spec (.of K), ⊤))
  exact isReduced_of_isAffine_isReduced _

/-- Smooth morphisms have geometrically reduced fibers. -/
theorem geometricallyReduced_of_smooth
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] : GeometricallyReduced f := by
  constructor
  intro K _ k Y p₁ p₂ h
  have : Smooth p₂ := MorphismProperty.of_isPullback h inferInstance
  exact reduced_of_smooth_field p₂

/-- Reducedness descends through a finite flat surjection. -/
theorem reduced_of_finite_flat_surjective
    {X Q : Scheme.{u}} (q : X ⟶ Q) [IsFinite q] [Flat q] [Surjective q]
    [IsReduced X] : IsReduced Q := by
  apply (IsReduced.iff_of_openCover Q Q.affineCover).mpr
  intro i
  let p := pullback.snd q (Q.affineCover.f i)
  have : IsAffine (pullback q (Q.affineCover.f i)) := isAffine_of_isAffineHom p
  have : IsReduced (pullback q (Q.affineCover.f i)) :=
    isReduced_of_isOpenImmersion (pullback.fst q (Q.affineCover.f i))
  have : _root_.IsReduced Γ(Q.affineCover.X i, ⊤) :=
    isReduced_of_injective p.appTop.hom
      ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine p).mp
        ⟨inferInstance, inferInstance⟩).injective
  exact isReduced_of_isAffine_isReduced _

/-- Geometric reducedness descends through a finite flat surjection. -/
theorem geometricallyReduced_of_comp
    {X Q S : Scheme.{u}} (q : X ⟶ Q) (b : Q ⟶ S)
    [IsFinite q] [Flat q] [Surjective q] [GeometricallyReduced (q ≫ b)] :
    GeometricallyReduced b := by
  constructor
  intro K _ k Y p₁ p₂ h
  have : IsReduced (pullback q p₁) :=
    GeometricallyReduced.geometrically_isReduced k (pullback.fst q p₁)
      (pullback.snd q p₁ ≫ p₂) ((IsPullback.of_hasPullback q p₁).paste_vert h)
  exact reduced_of_finite_flat_surjective (pullback.snd q p₁)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced
