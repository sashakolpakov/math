import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.FormTransport

/-! # Form Section Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormSectionIso

noncomputable section

/-! A quotient-coordinate isomorphism and a local form-section
isomorphism combine to an isomorphism over the ambient ring. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (B : Type u) [CommRing B] [Algebra R B] [Algebra A B]
  (N : Type u) [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
  (e : (A ⧸ I) ≃ₐ[R] B) (he : ∀ a : A, e (Ideal.Quotient.mk I a) = algebraMap A B a)
  (n : ℕ) (eN : N ≃ₗ[B] ⋀[B]^n Ω[B⁄R])

def map : (⋀[A ⧸ I]^n Ω[A ⧸ I⁄R]) →ₗ[A] N where
  toFun ω := eN.symm (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.isoMk e).hom n ω)
  map_add' ω η := by rw [map_add, map_add]
  map_smul' a ω := by
    change eN.symm (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.isoMk e).hom n
      ((Ideal.Quotient.mk I a) • ω)) = a • eN.symm (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.isoMk e).hom n ω)
    rw [AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_smul, map_smul]
    change e (Ideal.Quotient.mk I a) • _ = a • _
    rw [he, algebraMap_smul]

def iso : (⋀[A ⧸ I]^n Ω[A ⧸ I⁄R]) ≃ₗ[A] N :=
  LinearEquiv.ofBijective (FormSectionIso.map R A I B N e he n eN)
    (eN.symm.bijective.comp
      (ConcreteCategory.bijective_of_isIso ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsFunctor n).map (CommAlgCat.isoMk e).hom)))

theorem iso_apply (ω : ⋀[A ⧸ I]^n Ω[A ⧸ I⁄R]) :
    iso R A I B N e he n eN ω = eN.symm (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.isoMk e).hom n ω) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.FormSectionIso
