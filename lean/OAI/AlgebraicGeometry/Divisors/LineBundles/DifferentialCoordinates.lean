import OAI.AlgebraicGeometry.Divisors.LineBundles.DifferentialEtaleCriterion
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Differential Coordinates -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DifferentialCoordinates.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual coordinates whose differentials form a basis give an étale algebra map -/

open KaehlerDifferential TensorProduct

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {ι : Type}

abbrev differentialCoordinateAlgebra (v : ι → S) : Algebra (MvPolynomial ι R) S :=
  (MvPolynomial.aeval v).toRingHom.toAlgebra

theorem differentialCoordinate_scalarTower (v : ι → S) :
    letI := differentialCoordinateAlgebra (R := R) v
    IsScalarTower R (MvPolynomial ι R) S := by
  let := differentialCoordinateAlgebra (R := R) v
  exact IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.aeval_C v r).symm

theorem differentialCoordinate_map_bijective (v : ι → S) (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (v i)) :
    letI := differentialCoordinateAlgebra (R := R) v
    letI := differentialCoordinate_scalarTower (R := R) v
    Function.Bijective (mapBaseChange R (MvPolynomial ι R) S) := by
  let := differentialCoordinateAlgebra (R := R) v
  let := differentialCoordinate_scalarTower (R := R) v
  let c := (mvPolynomialBasis R ι).baseChange S
  let e := c.equiv b (Equiv.refl ι)
  have he : mapBaseChange R (MvPolynomial ι R) S = e.toLinearMap := by
    apply c.ext
    intro i
    have hi : mapBaseChange R (MvPolynomial ι R) S (c i) = D R S (v i) := by
      dsimp only [c]
      rw [Module.Basis.baseChange_apply, mvPolynomialBasis_apply, mapBaseChange_tmul, map_D, one_smul]
      exact congrArg (D R S) (MvPolynomial.aeval_X (R := R) v i)
    exact hi.trans ((hb i).symm.trans (c.equiv_apply (b' := b) (e := Equiv.refl ι) i).symm)
  exact he ▸ e.bijective

theorem differentialCoordinate_formallyEtale [Algebra.FormallySmooth R S]
    (v : ι → S) (b : Module.Basis ι S Ω[S⁄R]) (hb : ∀ i, b i = D R S (v i)) :
    letI := differentialCoordinateAlgebra (R := R) v
    Algebra.FormallyEtale (MvPolynomial ι R) S := by
  let := differentialCoordinateAlgebra (R := R) v
  let := differentialCoordinate_scalarTower (R := R) v
  exact DifferentialEtaleCriterion.BundleCycles.formallyEtale_of_differential_bijective R (MvPolynomial ι R) S
    (differentialCoordinate_map_bijective v b hb)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DifferentialCoordinates.BundleCycles
