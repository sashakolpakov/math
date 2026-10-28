import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Open Immersion Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.OpenImmersionPoints

noncomputable section

/-!
# Relative points of an open subscheme

The universal property of an actual open immersion lifts exactly those scheme
maps whose underlying image is contained in its open image. The lift respects
the base automatically. For complex-valued points, the image condition reduces
to membership of their unique underlying scheme point.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Lift a relative test point through an open immersion when its image lies
inside the open subscheme. Base compatibility follows from the lift equation. -/
def openImmersion_relativeLift {S : Scheme.{u}} {T U X : Over S}
    (i : U ⟶ X) [IsOpenImmersion i.left] (p : T ⟶ X)
    (hp : Set.range p.left ⊆ Set.range i.left) : T ⟶ U :=
  Over.homMk (IsOpenImmersion.lift i.left p.left hp) (by
    rw [← Over.w i, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w p])

@[reassoc (attr := simp)]
theorem openImmersion_relativeLift_fac {S : Scheme.{u}} {T U X : Over S}
    (i : U ⟶ X) [IsOpenImmersion i.left] (p : T ⟶ X)
    (hp : Set.range p.left ⊆ Set.range i.left) :
    openImmersion_relativeLift i p hp ≫ i = p := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac i.left p.left hp

/-- This relative lift is unique, by monomorphy of the open immersion. -/
theorem openImmersion_relativeLift_unique {S : Scheme.{u}} {T U X : Over S}
    (i : U ⟶ X) [IsOpenImmersion i.left] (p : T ⟶ X)
    (hp : Set.range p.left ⊆ Set.range i.left) (q : T ⟶ U) (hq : q ≫ i = p) :
    q = openImmersion_relativeLift i p hp := by
  let : Mono i := Over.mono_of_mono_left i
  apply (cancel_mono i).mp
  exact hq.trans (openImmersion_relativeLift_fac i p hp).symm

/-- Relative points of an open subscheme are exactly relative points whose
scheme-theoretic image lies inside that open subscheme. -/
def openImmersion_relativePointEquiv {S : Scheme.{u}} {T U X : Over S}
    (i : U ⟶ X) [IsOpenImmersion i.left] :
    (T ⟶ U) ≃ {p : T ⟶ X // Set.range p.left ⊆ Set.range i.left} where
  toFun q := ⟨q ≫ i, by
    rintro z ⟨t, rfl⟩
    exact ⟨q.left t, (Scheme.Hom.comp_apply q.left i.left t).symm⟩⟩
  invFun p := openImmersion_relativeLift i p.val p.property
  left_inv q := (openImmersion_relativeLift_unique i (q ≫ i) _ q rfl).symm
  right_inv p := Subtype.ext (openImmersion_relativeLift_fac i p.val p.property)

@[simp]
theorem openImmersion_relativePointEquiv_apply_val {S : Scheme.{u}} {T U X : Over S}
    (i : U ⟶ X) [IsOpenImmersion i.left] (q : T ⟶ U) :
    (openImmersion_relativePointEquiv i q).val = q ≫ i := rfl

/-- A complex point has singleton scheme-theoretic image, so containment in an
open image is equivalent to membership of its unique point. -/
theorem complexPoint_range_subset_iff {U X : Over ProjectiveSpace.complexBase} (i : U ⟶ X)
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) :
    Set.range p.left ⊆ Set.range i.left ↔ p.left (default : ProjectiveSpace.complexBase) ∈ Set.range i.left := by
  let : Unique (Over.mk (𝟙 ProjectiveSpace.complexBase)).left := inferInstanceAs (Unique ProjectiveSpace.complexBase)
  rw [Set.range_unique, Set.singleton_subset_iff]

/-- An open immersion induces a bijection onto the complex points whose
underlying point lies in the open image. -/
def openImmersion_complexPointEquiv {U X : Over ProjectiveSpace.complexBase}
    (i : U ⟶ X) [IsOpenImmersion i.left] :
    (Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ U) ≃
      {p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X // p.left (default : ProjectiveSpace.complexBase) ∈ Set.range i.left} :=
  (openImmersion_relativePointEquiv i).trans
    (Equiv.subtypeEquivRight (complexPoint_range_subset_iff i))

@[simp]
theorem openImmersion_complexPointEquiv_apply_val {U X : Over ProjectiveSpace.complexBase}
    (i : U ⟶ X) [IsOpenImmersion i.left] (q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ U) :
    (openImmersion_complexPointEquiv i q).val = q ≫ i := rfl

/-- The point map of an open immersion is injective. -/
theorem openImmersion_complexPointMap_injective {U X : Over ProjectiveSpace.complexBase}
    (i : U ⟶ X) [IsOpenImmersion i.left] :
    Function.Injective (fun q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ U => q ≫ i) := by
  intro q r h
  apply (openImmersion_complexPointEquiv i).injective
  exact Subtype.ext h

/-- Exact set-theoretic image of the complex-point map. -/
theorem range_openImmersion_complexPointMap {U X : Over ProjectiveSpace.complexBase}
    (i : U ⟶ X) [IsOpenImmersion i.left] :
    Set.range (fun q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ U => q ≫ i) =
      {p | p.left (default : ProjectiveSpace.complexBase) ∈ Set.range i.left} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact (openImmersion_complexPointEquiv i q).property
  · intro hp
    refine ⟨(openImmersion_complexPointEquiv i).symm ⟨p, hp⟩, ?_⟩
    exact congrArg Subtype.val ((openImmersion_complexPointEquiv i).apply_symm_apply ⟨p, hp⟩)

/-- Every complex point in the open image has a unique relative lift. -/
theorem openImmersion_complexPoint_existsUnique {U X : Over ProjectiveSpace.complexBase}
    (i : U ⟶ X) [IsOpenImmersion i.left]
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) (hp : p.left (default : ProjectiveSpace.complexBase) ∈ Set.range i.left) :
    ∃! q : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ U, q ≫ i = p := by
  let q := (openImmersion_complexPointEquiv i).symm ⟨p, hp⟩
  have hq : q ≫ i = p :=
    congrArg Subtype.val ((openImmersion_complexPointEquiv i).apply_symm_apply ⟨p, hp⟩)
  refine ⟨q, hq, ?_⟩
  intro r hr
  exact openImmersion_complexPointMap_injective i (hr.trans hq.symm)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.OpenImmersionPoints
