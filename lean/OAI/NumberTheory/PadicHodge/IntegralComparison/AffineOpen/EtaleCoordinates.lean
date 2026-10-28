import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase

/-! # Etale Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates

noncomputable section

/-!
# IntegralComparison: affine subopens inherit the actual finite étale coordinates of their charts
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase

universe u

variable (k : Type u) [CommRing k] (X : Over (Spec (CommRingCat.of k)))
  (U : X.left.Opens) (hU : IsAffineOpen U) (C : Type u) [CommRing C]
  (g : Spec (CommRingCat.of C) ⟶ X.left) [IsOpenImmersion g] (h : U ≤ g.opensRange)
  (σ : Type u) [Algebra (MvPolynomial σ k) C]

@[instance_reducible]
def polynomialAlgebra : Algebra (MvPolynomial σ k) ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U)) :=
  ((SectionBase.ringMap k X U hU C g h).hom.comp (algebraMap (MvPolynomial σ k) C)).toAlgebra

variable [Algebra.Etale (MvPolynomial σ k) C]

theorem etale : letI := polynomialAlgebra k X U hU C g h σ
    Algebra.Etale (MvPolynomial σ k) ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U)) := by
  let := polynomialAlgebra k X U hU C g h σ
  apply RingHom.etale_algebraMap.mp
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale (MvPolynomial σ k) C)))
    (SectionBase.ringMap_etale k X U hU C g h)

variable [Algebra k C] [IsScalarTower k (MvPolynomial σ k) C]
  (hg : g ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k C)))

omit [Algebra.Etale (MvPolynomial σ k) C] in
include hg in
theorem tower : letI := polynomialAlgebra k X U hU C g h σ
    IsScalarTower k (MvPolynomial σ k) ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U)) := by
  let := polynomialAlgebra k X U hU C g h σ
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap k ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U)) r =
    (SectionBase.ringMap k X U hU C g h).hom (algebraMap (MvPolynomial σ k) C (algebraMap k (MvPolynomial σ k) r))
  rw [← IsScalarTower.algebraMap_apply]
  exact (ConcreteCategory.congr_hom (SectionBase.ringMap_base k X U hU C g h hg) r).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates
