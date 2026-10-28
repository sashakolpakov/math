import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Resolution
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.DimensionFunctor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Dimension Bound -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.DimensionBound

noncomputable section

/-! A polynomial ring in n variables over a field has projective dimension
at most n for every module. The proof iterates the actual induced-module
short exact sequence, starting with vector spaces. -/

open _root_.CategoryTheory _root_.Polynomial
open scoped TensorProduct

universe u

theorem polynomial_module_bound (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [Module R[X] M] [IsScalarTower R R[X] M] (d : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R M) d] :
    HasProjectiveDimensionLE (ModuleCat.of R[X] M) (d + 1) := by
  let : HasProjectiveDimensionLE (ModuleCat.of R[X] (R[X] ⊗[R] M)) d :=
    Projective.DimensionFunctor.preserves_bound (Flat.Extension.baseChange R R[X])
      (ModuleCat.of R M) d
  let : HasProjectiveDimensionLE (ModuleCat.of R[X] (PolynomialModule R M)) d :=
    ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
      (M := ModuleCat.of R[X] (R[X] ⊗[R] M))
      (PolynomialModule.polynomialTensorProductLEquivPolynomialModule R M) d
  exact (Resolution.shortExact R M).hasProjectiveDimensionLT_X₃ (d + 1)
    (show HasProjectiveDimensionLE (ModuleCat.of R[X] (PolynomialModule R M)) d from inferInstance)
    (hasProjectiveDimensionLT_of_ge (ModuleCat.of R[X] (PolynomialModule R M))
      (d + 1) (d + 2) (by omega))

def GlobalBound (R : Type u) [CommRing R] (d : ℕ) : Prop :=
  ∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M d

attribute [local instance] RingHomInvPair.of_ringEquiv in
theorem bound_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (d : ℕ) (h : GlobalBound R d) : GlobalBound S d := by
  intro M
  let : Module R M := Module.compHom M e.toRingHom
  let : HasProjectiveDimensionLE (ModuleCat.of R M) d := h (ModuleCat.of R M)
  let eM : (ModuleCat.of R M) ≃ₛₗ[RingHomClass.toRingHom e] M :=
    { AddEquiv.refl M with map_smul' := by intros; rfl }
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e eM d

theorem polynomial_bound (R : Type u) [CommRing R] (d : ℕ) (h : GlobalBound R d) :
    GlobalBound R[X] (d + 1) := by
  intro M
  let : Module R M := Module.compHom M (algebraMap R R[X])
  let : IsScalarTower R R[X] M := IsScalarTower.of_algebraMap_smul (by intros; rfl)
  let : HasProjectiveDimensionLE (ModuleCat.of R M) d := h (ModuleCat.of R M)
  exact polynomial_module_bound R M d

theorem field_bound (K : Type u) [Field K] : GlobalBound K 0 := by
  intro M
  exact (projective_iff_hasProjectiveDimensionLE_zero M).mp inferInstance

theorem mvPolynomial_bound (K : Type u) [Field K] (n : ℕ) :
    GlobalBound (MvPolynomial (Fin n) K) n := by
  induction n with
  | zero =>
    exact bound_of_ringEquiv (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toRingEquiv.symm
      0 (field_bound K)
  | succ n ih =>
    exact bound_of_ringEquiv (MvPolynomial.finSuccEquiv K n).toRingEquiv.symm
      (n + 1) (polynomial_bound (MvPolynomial (Fin n) K) n ih)

theorem mvPolynomial_bound_of_zero (R : Type u) [CommRing R]
    (h : GlobalBound R 0) (n : ℕ) : GlobalBound (MvPolynomial (Fin n) R) n := by
  induction n with
  | zero => exact bound_of_ringEquiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.symm 0 h
  | succ n ih =>
    exact bound_of_ringEquiv (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm
      (n + 1) (polynomial_bound (MvPolynomial (Fin n) R) n ih)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.DimensionBound
