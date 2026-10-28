import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductRigidity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProperProductOpenGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Product Constancy -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductConstancy.Construction

noncomputable section

/-!
# Completion: the locus of fibers where a product map is constant

This locus is defined from the actual scheme equalizer. Its membership
criterion therefore retains scheme-theoretic agreement, rather than only
equality of the underlying point maps.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S : Scheme.{u}}

/-- The actual fiber product as an object over the ground scheme. -/
def properProductOver (A B : Over S) : Over S :=
  Over.mk (pullback.snd A.hom B.hom ≫ B.hom)

/-- Projection to the second factor over the ground scheme. -/
def properProductProjectionOver (A B : Over S) : properProductOver A B ⟶ B :=
  Over.homMk (pullback.snd A.hom B.hom) rfl

/-- The product with an open in the second factor, over the ground scheme. -/
def properProductOpenOver (A B : Over S) (U : B.left.Opens) : Over S :=
  Over.mk (pullback.snd A.hom (U.ι ≫ B.hom) ≫ U.ι ≫ B.hom)

/-- The open-product inclusion as a map over the ground scheme. -/
def properProductOpenMapOver (A B : Over S) (U : B.left.Opens) :
    properProductOpenOver A B U ⟶ properProductOver A B :=
  Over.homMk (ProductOpen.Construction.properProductOpenMap A.hom B.hom U) (by
    change ProductOpen.Construction.properProductOpenMap A.hom B.hom U ≫ pullback.snd A.hom B.hom ≫ B.hom = _
    simp [properProductOpenOver])

variable {K : Type u} [Field K] (A B Z : Over (Spec (CommRingCat.of K)))
  (e : Spec (CommRingCat.of K) ⟶ A.left) (he : e ≫ A.hom = 𝟙 _)

/-- The section of the second projection as a map over the field. -/
def properProductSectionOver : B ⟶ properProductOver A B :=
  Over.homMk (AffineBaseChange.Construction.properProductSection A.hom B.hom e he) (by
    simp [AffineBaseChange.Construction.properProductSection, properProductOver])

/-- The map obtained by evaluating on the section and projecting back to the second factor. -/
def properProductConstantMap (f : properProductOver A B ⟶ Z) : properProductOver A B ⟶ Z :=
  properProductProjectionOver A B ≫ properProductSectionOver A B e he ≫ f

/-- Fibers lying entirely in the actual equalizer of the map and its section-wise constant map. -/
def properProductConstancySet (f : properProductOver A B ⟶ Z) : Set B.left :=
  (pullback.snd A.hom B.hom ''
    (Set.range (equalizer.ι f (properProductConstantMap A B Z e he f)).left)ᶜ)ᶜ

theorem mem_properProductConstancySet (f : properProductOver A B ⟶ Z) (y : B.left) :
    y ∈ properProductConstancySet A B Z e he f ↔
      ∀ t : (pullback A.hom B.hom : Scheme.{u}), pullback.snd A.hom B.hom t = y →
        t ∈ Set.range (equalizer.ι f (properProductConstantMap A B Z e he f)).left := by
  constructor
  · intro h t ht
    by_contra hn
    exact h ⟨t, hn, ht⟩
  · intro h
    rintro ⟨t, hn, ht⟩
    exact hn (h t ht)

/-- Membership forces the map on that fiber to have the value specified by the section. -/
theorem properProductConstancySet_value (f : properProductOver A B ⟶ Z)
    (y : B.left) (hy : y ∈ properProductConstancySet A B Z e he f)
    (t : (pullback A.hom B.hom : Scheme.{u})) (ht : pullback.snd A.hom B.hom t = y) :
    f.left t = f.left (AffineBaseChange.Construction.properProductSection A.hom B.hom e he y) := by
  obtain ⟨w, hw⟩ := (mem_properProductConstancySet A B Z e he f y).mp hy t ht
  have h := congrArg (fun k : equalizer f (properProductConstantMap A B Z e he f) ⟶ Z =>
    k.left w) (equalizer.condition f (properProductConstantMap A B Z e he f))
  change f.left ((equalizer.ι f (properProductConstantMap A B Z e he f)).left w) =
    f.left (AffineBaseChange.Construction.properProductSection A.hom B.hom e he
      (pullback.snd A.hom B.hom ((equalizer.ι f (properProductConstantMap A B Z e he f)).left w))) at h
  rwa [hw, ht] at h

/-- A local factorization puts every fiber over that base open in the constancy locus. -/
theorem properProductConstancySet_of_open_factorization
    (f : properProductOver A B ⟶ Z) (U : B.left.Opens)
    (h : ProductOpen.Construction.properProductOpenMap A.hom B.hom U ≫ f.left =
      pullback.snd A.hom (U.ι ≫ B.hom) ≫ U.ι ≫
        AffineBaseChange.Construction.properProductSection A.hom B.hom e he ≫ f.left) :
    (U : Set B.left) ⊆ properProductConstancySet A B Z e he f := by
  have h' : properProductOpenMapOver A B U ≫ f =
      properProductOpenMapOver A B U ≫ properProductConstantMap A B Z e he f := by
    apply Over.OverMorphism.ext
    change ProductOpen.Construction.properProductOpenMap A.hom B.hom U ≫ f.left =
      ProductOpen.Construction.properProductOpenMap A.hom B.hom U ≫ pullback.snd A.hom B.hom ≫
        AffineBaseChange.Construction.properProductSection A.hom B.hom e he ≫ f.left
    simpa only [ProductOpen.Construction.properProductOpenMap_snd_assoc, Category.assoc] using h
  intro y hy
  apply (mem_properProductConstancySet A B Z e he f y).mpr
  intro t ht
  have ht' : t ∈ Set.range (ProductOpen.Construction.properProductOpenMap A.hom B.hom U) := by
    rw [ProperProductOpenGeometry.Construction.properProductOpen_range]
    change pullback.snd A.hom B.hom t ∈ U
    rw [ht]
    exact hy
  obtain ⟨w, rfl⟩ := ht'
  refine ⟨(equalizer.lift (properProductOpenMapOver A B U) h').left w, ?_⟩
  exact congrArg (fun k : properProductOpenOver A B U ⟶ properProductOver A B => k.left w)
    (equalizer.lift_ι (properProductOpenMapOver A B U) h')

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductConstancy.Construction
