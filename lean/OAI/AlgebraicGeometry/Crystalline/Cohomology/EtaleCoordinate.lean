import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Etale Coordinate -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations

noncomputable section

/-! # Coordinate derivations on an etale polynomial lift over an arbitrary base ring -/

universe u v w

variable (R A : Type u) (σ : Type v) [CommRing R] [CommRing A] [Algebra R A]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]

def coordinate (i : σ) : A := algebraMap (MvPolynomial σ R) A (MvPolynomial.X i)

def basis : Module.Basis σ A (KaehlerDifferential R A) :=
  ((KaehlerDifferential.mvPolynomialBasis R σ).baseChange A).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial σ R) A)

theorem basis_apply (i : σ) : basis R A σ i = KaehlerDifferential.D R A (coordinate R A σ i) := by
  rw [basis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  exact ((LinearEquiv.symm_apply_eq
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial σ R) A)).mp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap R (MvPolynomial σ R) A
      (MvPolynomial.X i))).symm

def derivation (i : σ) : Derivation R A A :=
  ((basis R A σ).coord i).compDer (KaehlerDifferential.D R A)

theorem derivation_coordinate [DecidableEq σ] (i j : σ) :
    derivation R A σ i (coordinate R A σ j) = if j = i then 1 else 0 := by
  change (basis R A σ).coord i (KaehlerDifferential.D R A (coordinate R A σ j)) = _
  rw [← basis_apply]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

variable {M : Type w} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]

theorem ext (D E : Derivation R A M)
    (h : ∀ i : σ, D (coordinate R A σ i) = E (coordinate R A σ i)) : D = E := by
  have he : D.liftKaehlerDifferential = E.liftKaehlerDifferential := by
    apply (basis R A σ).ext
    intro i
    rw [basis_apply, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h i
  apply Derivation.ext
  intro a
  rw [← Derivation.liftKaehlerDifferential_comp_D D a,
    ← Derivation.liftKaehlerDifferential_comp_D E a, he]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations
