import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientCover

/-! # Family Locality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyLocality

noncomputable section

/-! The actual Hilbert-family conditions are local on the test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X : Over S) {T : Over S} {J : Type u}
variable (U : J → Over S) (f : ∀ i, U i ⟶ T) [∀ i, IsOpenImmersion (f i).left]
variable (hcover : ∀ t : T.left, ∃ i, ∃ y : (U i).left, (f i).left y = t)

def testOpenCover : T.left.OpenCover.{u} where
  I₀ := J
  X i := (U i).left
  f i := (f i).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨hcover, inferInstance⟩

include hcover in
theorem familyProjection_property_of_openCover
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (I : (Functor.ambient X T).IdealSheafData)
    (h : ∀ i, P (Functor.familyProjection X (I.comap (Functor.ambientMap X (f i))))) : P (Functor.familyProjection X I) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := P) (testOpenCover U f hcover)).mpr
  intro i
  change J at i
  change P (pullback.snd (Functor.familyProjection X I) (f i).left)
  let hp := (Functor.family_isPullback X (f i) I).flip
  rw [← hp.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
  exact h i

include hcover in
theorem isFamily_of_openCover (I : (Functor.ambient X T).IdealSheafData)
    (h : ∀ i, Functor.IsFamily X (I.comap (Functor.ambientMap X (f i)))) : Functor.IsFamily X I := by
  have : IsZariskiLocalAtTarget @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{u}) (Q := RingHom.Flat)
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation.{u}) (Q := RingHom.FinitePresentation)
  exact ⟨familyProjection_property_of_openCover X U f hcover (@Flat) I (fun i => (h i).1),
    familyProjection_property_of_openCover X U f hcover (@IsProper) I (fun i => (h i).2.1),
    familyProjection_property_of_openCover X U f hcover (@LocallyOfFinitePresentation) I (fun i => (h i).2.2)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyLocality
