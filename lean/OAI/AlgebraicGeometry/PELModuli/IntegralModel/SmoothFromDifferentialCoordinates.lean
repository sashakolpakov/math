import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolynomialEtaleCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleCancellationOf
import Mathlib.RingTheory.Smooth.Fiber

/-! # Smooth From Differential Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothFromDifferentialCoordinates

noncomputable section

/-! Differential coordinates on the target of a finite etale cover
are smooth coordinates when the covering algebra is smooth. -/

open TensorProduct KaehlerDifferential _root_.Module

theorem smooth_of_differential_coordinates_and_finite_etale_cover
    (R A B : Type*) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.FaithfullyFlat A B] [Module.Finite A B]
    [Algebra.Etale A B] [Algebra.Smooth R B]
    {ι : Type} [Finite ι] (a : ι → A) (b : Basis ι A Ω[A⁄R])
    (hb : ∀ i, b i = D R A (a i)) : Algebra.Smooth R A := by
  let P := MvPolynomial ι R
  let φ : P →ₐ[R] A := MvPolynomial.aeval a
  let : Algebra P A := φ.toRingHom.toAlgebra
  let : Algebra P B := (IsScalarTower.toAlgHom R A B |>.comp φ).toRingHom.toAlgebra
  have : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R P B := IsScalarTower.to₁₂₄ R P A B
  let c := (b.baseChange B).map (tensorKaehlerEquivOfFormallyEtale R A B)
  have hc (i : ι) : c i = D R B (algebraMap P B (MvPolynomial.X i)) := by
    simp only [c, Basis.map_apply, Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, hb, map_D]
    congr 1
    change algebraMap A B (a i) = algebraMap A B (MvPolynomial.aeval a (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X]
  have : Algebra.FormallyEtale P B := PolynomialEtaleCoordinates.polynomial_coordinates_formallyEtale R B ι c hc
  have : Algebra.FiniteType P A := Algebra.FiniteType.of_restrictScalars_finiteType R P A
  have : Algebra.FiniteType P B := Algebra.FiniteType.of_restrictScalars_finiteType R P B
  have : Algebra.FinitePresentation P A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FinitePresentation P B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale P B := ⟨inferInstance, inferInstance⟩
  have : Algebra.FormallyUnramified P A :=
    AbelianScheme.TorsionQuotient.EtaleCancellationOf.EtaleCancellation.algebra_unramified P A B
  have : Module.Flat P A := Quotients.FiniteDescent.FlatFiniteness.Construction.FlatFinitenessDescent.flat
    (R := P) (B := A) (A := B) (FaithfulSMul.algebraMap_injective A B)
  have : Algebra.Etale P A := Algebra.Etale.of_formallyUnramified_of_flat
  have : Algebra.Smooth R P := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.comp R P A

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothFromDifferentialCoordinates
