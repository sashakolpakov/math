import OAI.AlgebraicGeometry.Crystalline.Cohomology.EtalePolynomialC

/-! # Etale Polynomial Tower -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.EtalePolynomialTower.EtalePolynomialPushoutCoordinates

noncomputable section

/-! An arbitrary coefficient pushout of an etale coordinate algebra inherits coordinates and the canonical full de Rham scalar isomorphism. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u
variable (R S A B σ : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]

attribute [local instance] EtalePolynomialC.EtalePolynomialTensorCoordinates.coordinateAlgebra
  EtalePolynomialC.EtalePolynomialTensorCoordinates.coordinateTower EtalePolynomialC.EtalePolynomialTensorCoordinates.etale
  Algebra.TensorProduct.rightAlgebra

local notation "Q" => MvPolynomial σ S
local notation "T" => S ⊗[R] A

@[instance_reducible]
def coordinateAlgebra : Algebra Q B :=
  ((Algebra.IsPushout.equiv R S A B).toRingHom.comp (algebraMap Q T)).toAlgebra

theorem coordinateTower :
    letI : Algebra Q B := coordinateAlgebra R S A B σ
    IsScalarTower S Q B := by
  let : Algebra Q B := coordinateAlgebra R S A B σ
  apply IsScalarTower.of_algebraMap_eq
  intro s
  change algebraMap S B s = Algebra.IsPushout.equiv R S A B
    (algebraMap Q T (algebraMap S Q s))
  exact ((Algebra.IsPushout.equiv R S A B).commutes s).symm.trans
    (congrArg (Algebra.IsPushout.equiv R S A B) (IsScalarTower.algebraMap_apply S Q T s))

def coordinateEquiv :
    letI : Algebra Q B := coordinateAlgebra R S A B σ
    T ≃ₐ[Q] B := by
  letI : Algebra Q B := coordinateAlgebra R S A B σ
  exact { __ := (Algebra.IsPushout.equiv R S A B).toRingEquiv, commutes' := fun _ => rfl }

theorem etale [Algebra.Etale (MvPolynomial σ R) A] :
    letI : Algebra Q B := coordinateAlgebra R S A B σ
    Algebra.Etale Q B := by
  let : Algebra Q B := coordinateAlgebra R S A B σ
  exact Algebra.Etale.of_equiv (coordinateEquiv R S A B σ)

variable [Algebra.Etale (MvPolynomial σ R) A] [Module.Flat R S] [LinearOrder σ]

def complexIso :
    (((NumberTheory.PadicHodge.GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor.{u, u} R S).mapHomologicalComplex (.up ℕ)).obj
      (DeRhamPresentationTo.DeRhamPresentation.complex R A)) ≅ DeRhamPresentationTo.DeRhamPresentation.complex S B := by
  letI : Algebra Q B := coordinateAlgebra R S A B σ
  letI : IsScalarTower S Q B := coordinateTower R S A B σ
  letI : Algebra.Etale Q B := etale R S A B σ
  exact EtaleDeRham.EtaleDeRhamScalarExtension.complexIso R S A B σ σ

theorem component (n : ℕ) : (complexIso R S A B σ).hom.f n =
    ModuleCat.ofHom (NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B n) := by
  let : Algebra Q B := coordinateAlgebra R S A B σ
  let : IsScalarTower S Q B := coordinateTower R S A B σ
  let : Algebra.Etale Q B := etale R S A B σ
  exact congrArg ModuleCat.ofHom (FormsTensorBaseChange.EtaleFormsTensorBaseChange.scalarEquiv_eq_map R S A B σ σ n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.EtalePolynomialTower.EtalePolynomialPushoutCoordinates
