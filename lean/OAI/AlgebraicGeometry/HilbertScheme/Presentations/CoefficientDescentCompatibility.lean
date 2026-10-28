import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IdealCoefficientBaseChange

/-! # Coefficient Descent Compatibility -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientDescentCompatibility

noncomputable section

/-! A coefficient ideal on a base change has matching extensions along
any two coefficient maps with the same composite to the original base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {R A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) [Flat f]
variable (K : X.IdealSheafData) (φ : R ⟶ A) (C : Ideal A)
variable (hC : Affine.IdealCoefficientTests.IsAffineIdealCoefficient A (pullback.snd f (Spec.map φ))
  (K.comap (pullback.fst f (Spec.map φ))) C)
include hC

theorem affineIdealCoefficient_test_composite {B : CommRingCat.{u}} (ψ : A ⟶ B) :
    K.comap (pullback.fst f (Spec.map (φ ≫ ψ))) = ⊥ ↔ C ≤ RingHom.ker ψ.hom := by
  have h := Affine.IdealCoefficientTests.affineIdealCoefficient_test A (pullback.snd f (Spec.map φ))
    (K.comap (pullback.fst f (Spec.map φ))) C hC ψ
  rwa [Presentations.Ideal.PullbackVanishing.pullback_ideal_vanishing_comp, ← Spec.map_comp] at h

theorem affineIdealCoefficient_descent_compatibility {D : CommRingCat.{u}}
    (a b : A ⟶ D) (hab : φ ≫ a = φ ≫ b) : C.map a.hom = C.map b.hom := by
  have ht (B : CommRingCat.{u}) (ψ : D ⟶ B) :
      C.map a.hom ≤ RingHom.ker ψ.hom ↔ C.map b.hom ≤ RingHom.ker ψ.hom := by
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap,
      RingHom.comap_ker, RingHom.comap_ker]
    change C ≤ RingHom.ker (a ≫ ψ).hom ↔ C ≤ RingHom.ker (b ≫ ψ).hom
    rw [← affineIdealCoefficient_test_composite f K φ C hC,
      ← affineIdealCoefficient_test_composite f K φ C hC, ← Category.assoc, hab, Category.assoc]
  apply le_antisymm
  · have h := ht (CommRingCat.of (D ⧸ C.map b.hom))
      (CommRingCat.ofHom (Ideal.Quotient.mk (C.map b.hom)))
    rw [CommRingCat.hom_ofHom, Ideal.mk_ker] at h
    exact h.mpr le_rfl
  · have h := ht (CommRingCat.of (D ⧸ C.map a.hom))
      (CommRingCat.ofHom (Ideal.Quotient.mk (C.map a.hom)))
    rw [CommRingCat.hom_ofHom, Ideal.mk_ker] at h
    exact h.mp le_rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientDescentCompatibility
