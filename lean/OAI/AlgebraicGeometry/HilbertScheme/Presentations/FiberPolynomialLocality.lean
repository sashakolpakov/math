import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberPolynomialBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FieldPointOpenLift

/-! # Fiber Polynomial Locality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberPolynomialLocality.Core

noncomputable section

/-! The exact field-fiber polynomial condition is local on the test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X : Over S} (B : Has.Core.ProjectivePresentation X)
variable {T : Over S} {J : Type u} (U : J → Over S) (f : ∀ i, U i ⟶ T)
variable [∀ i, IsOpenImmersion (f i).left]
variable (hcover : ∀ t : T.left, ∃ i, ∃ y : (U i).left, (f i).left y = t)

include hcover in
theorem hasFiberHilbertPolynomial_of_openCover (I : Hilbert.Functor.Family X T) (P : Polynomial ℚ)
    (h : ∀ i, Has.Core.HasFiberHilbertPolynomial B (Hilbert.Functor.pullbackFamily X (f i) I) P) :
    Has.Core.HasFiberHilbertPolynomial B I P := by
  intro K _ a
  let C := Hilbert.FamilyLocality.testOpenCover U f hcover
  obtain ⟨i, β, hβ⟩ := FieldPointOpenLift.fieldPoint_lift_openCover C a
  change J at i
  let b : Spec (CommRingCat.of K) ⟶ (U i).left := β
  have hb : b ≫ (f i).left = a := hβ
  have hbase : b ≫ (U i).hom = a ≫ T.hom := by
    rw [← (f i).w, ← Category.assoc, hb]
  have H := FiberPolynomialBaseChange.Core.hasFiberHilbertPolynomial_at B (Hilbert.Functor.pullbackFamily X (f i) I) P
    (h i) K b (a ≫ T.hom) hbase
  dsimp only at H ⊢
  rw [← Hilbert.Functor.pullbackFamily_comp] at H
  have he : (Over.homMk b hbase : Over.mk (a ≫ T.hom) ⟶ U i) ≫ f i =
      (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) := Over.OverMorphism.ext hb
  rw [he] at H
  exact H

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberPolynomialLocality.Core
