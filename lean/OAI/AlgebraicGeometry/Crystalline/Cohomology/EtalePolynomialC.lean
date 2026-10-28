import OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleQuotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Etale.Basic

/-! # Etale Polynomial C -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.EtalePolynomialC.EtalePolynomialTensorCoordinates

noncomputable section

/-! Actual scalar-extended etale charts inherit their polynomial coordinate presentation. -/

open _root_.CategoryTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u
variable (R S A σ : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [Algebra R A] [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]

local notation "P" => MvPolynomial σ R
local notation "Q" => MvPolynomial σ S
local notation "D" => Q ⊗[P] A
local notation "T" => S ⊗[R] A

def polynomialEquiv : P ⊗[R] S ≃ₐ[P] Q where
  __ := (Algebra.TensorProduct.comm R P S).trans ((MvPolynomial.algebraTensorAlgEquiv R S).restrictScalars R)
  commutes' f := by
    change MvPolynomial.algebraTensorAlgEquiv R S (1 ⊗ₜ[R] f) = MvPolynomial.map (algebraMap R S) f
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

theorem polynomialEquiv_symm_C (s : S) : (polynomialEquiv R S σ).symm (MvPolynomial.C s) = (1 : P) ⊗ₜ[R] s := by
  apply (polynomialEquiv R S σ).injective
  rw [AlgEquiv.apply_symm_apply]
  change MvPolynomial.C s = MvPolynomial.algebraTensorAlgEquiv R S (s ⊗ₜ[R] (1 : P))
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, map_one]
  simp only [MvPolynomial.smul_eq_C_mul, mul_one]

def ringEquiv : D ≃ₐ[R] T :=
  ((Algebra.TensorProduct.congr (polynomialEquiv R S σ).symm
      (AlgEquiv.refl : A ≃ₐ[P] A)).restrictScalars R).trans
    (((Algebra.TensorProduct.comm P (P ⊗[R] S) A).restrictScalars R).trans
      (((Algebra.TensorProduct.cancelBaseChange R P P A S).restrictScalars R).trans
        (Algebra.TensorProduct.comm R A S)))

theorem ringEquiv_C_tmul_one (s : S) : ringEquiv R S A σ (MvPolynomial.C s ⊗ₜ[P] (1 : A)) = s ⊗ₜ[R] (1 : A) := by
  simp only [ringEquiv, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom,
    polynomialEquiv_symm_C, map_one, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]

def scalarEquiv : D ≃ₐ[S] T where
  __ := ringEquiv R S A σ
  commutes' s := ringEquiv_C_tmul_one R S A σ s

instance coordinateAlgebra : Algebra Q T :=
  ((scalarEquiv R S A σ).toRingHom.comp (algebraMap Q D)).toAlgebra

instance coordinateTower : IsScalarTower S Q T :=
  IsScalarTower.of_algebraMap_eq (fun s => ((scalarEquiv R S A σ).commutes s).symm)

def coordinateEquiv : D ≃ₐ[Q] T where
  __ := (scalarEquiv R S A σ).toRingEquiv
  commutes' _ := rfl

instance etale [Algebra.Etale P A] : Algebra.Etale Q T :=
  Algebra.Etale.of_equiv (coordinateEquiv R S A σ)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable [Algebra.Etale (MvPolynomial σ R) A] [Module.Flat R S] [LinearOrder σ]

def complexIso : (((NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S).mapHomologicalComplex (.up ℕ)).obj
    (DeRhamPresentationTo.DeRhamPresentation.complex R A)) ≅ DeRhamPresentationTo.DeRhamPresentation.complex S T :=
  EtaleDeRham.EtaleDeRhamScalarExtension.complexIso R S A T σ σ

def quotientIso (I : Ideal R) :
    (((NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S).mapHomologicalComplex (.up ℕ)).obj
      (DeRhamPresentationTo.DeRhamPresentation.complex R (A ⧸ I.map (algebraMap R A)))) ≅
    DeRhamPresentationTo.DeRhamPresentation.complex S (T ⧸ (I.map (algebraMap R S)).map (algebraMap S T)) :=
  EtaleQuotient.EtaleQuotientScalarExtension.complexIso R S A T σ σ I

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.EtalePolynomialC.EtalePolynomialTensorCoordinates
