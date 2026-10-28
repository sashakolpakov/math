import OAI.AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Integral Homology Coefficients -/

namespace OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients

noncomputable section

/-!
# Integral-to-scalar coefficients on actual singular homology

The finite coefficient map preserves cycles and boundaries. It therefore
descends to the existing categorical homology groups via their proved
kernel/image description. The representative formula fixes this map uniquely.
-/

open _root_.CategoryTheory

open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

private def integerLinearOfAdditive {M N : Type}
    [AddCommGroup M] [AddCommGroup N]
    {modM : Module ℤ M} {modN : Module ℤ N} (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    change f (modM.smul r x) = modN.smul r (f x)
    simp only [int_smul_eq_zsmul, map_zsmul]

private def descendLinear {S : Type} [Ring S]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    {modM : Module S M} {modN : Module S N} {modP : Module S P}
    (π : M →ₗ[S] N) (hπ : Function.Surjective π) (f : M →ₗ[S] P)
    (hf : LinearMap.ker π ≤ LinearMap.ker f) : N →ₗ[S] P :=
  ((LinearMap.ker π).liftQ f hf).comp (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

private theorem descendLinear_apply {S : Type} [Ring S]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    {modM : Module S M} {modN : Module S N} {modP : Module S P}
    (π : M →ₗ[S] N) (hπ : Function.Surjective π) (f : M →ₗ[S] P)
    (hf : LinearMap.ker π ≤ LinearMap.ker f) (x : M) :
    descendLinear π hπ f hf (π x) = f x := by
  simp only [descendLinear, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

variable {R : Type} [CommRing R]

/-- The finite integral coefficient map restricted to actual cycles. -/
def integralToScalarSimplicialCycles (K : SSet.{0}) (n : ℕ) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K) n →ₗ[ℤ]
      Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) n :=
  integerLinearOfAdditive
    { toFun z := ⟨IntegralCapCoefficients.integralToScalarSimplicial (R := R) K n z.val, by
        change (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).d n
          ((ComplexShape.down ℕ).next n)
          (IntegralCapCoefficients.integralToScalarSimplicial (R := R) K n z.val) = 0
        rw [← IntegralCapCoefficients.integralToScalarSimplicial_d,
          Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K) n _ z, map_zero]⟩
      map_zero' := by
        apply Subtype.ext
        exact map_zero (IntegralCapCoefficients.integralToScalarSimplicial (R := R) K n)
      map_add' z w := by
        apply Subtype.ext
        exact map_add (IntegralCapCoefficients.integralToScalarSimplicial (R := R) K n) z.val w.val }

@[simp]
theorem integralToScalarSimplicialCycles_val (K : SSet.{0}) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K) n) :
    (integralToScalarSimplicialCycles (R := R) K n z).val =
      IntegralCapCoefficients.integralToScalarSimplicial (R := R) K n z.val := rfl

/-- Change the coefficients of actual categorical simplicial homology from
integers to the scalar ring. No choice of a new homology model is made. -/
def integralToScalarSimplicialHomology (K : SSet.{0}) (n : ℕ) :
    (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).homology n →ₗ[ℤ]
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).homology n :=
  descendLinear (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K) n)
    (Cohomology.Singular.ChainRepresentatives.chainClass_surjective (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K) n)
    (integerLinearOfAdditive
      ((Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) n).toAddMonoidHom.comp
        (integralToScalarSimplicialCycles (R := R) K n).toAddMonoidHom))
    (by
      intro z hz
      rcases (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists
        (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K) n z).mp hz with ⟨w, hw⟩
      change Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) n
        (integralToScalarSimplicialCycles (R := R) K n z) = 0
      apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) n _).mpr
      refine ⟨IntegralCapCoefficients.integralToScalarSimplicial (R := R) K (n + 1) w, ?_⟩
      rw [← IntegralCapCoefficients.integralToScalarSimplicial_d, hw]
      rfl)

/-- A represented integral class is sent to the class of the same cycle
with its coefficients mapped to the scalar ring. -/
@[simp]
theorem integralToScalarSimplicialHomology_chainClass (K : SSet.{0}) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K) n) :
    integralToScalarSimplicialHomology (R := R) K n
        (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K) n z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K) n
        (integralToScalarSimplicialCycles (R := R) K n z) := by
  dsimp only [integralToScalarSimplicialHomology]
  rw [descendLinear_apply]
  rfl

theorem integralToScalarSimplicialCycles_naturality {K L : SSet.{0}} (f : K ⟶ L)
    (n : ℕ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K) n) :
    Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) f) n
        (integralToScalarSimplicialCycles (R := R) K n z) =
      integralToScalarSimplicialCycles (R := R) L n
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℤ) f) n z) := by
  apply Subtype.ext
  exact IntegralCapCoefficients.integralToScalarSimplicial_naturality (R := R) f n z.val

/-- The descended coefficient map is natural on native simplicial homology. -/
theorem integralToScalarSimplicialHomology_naturality {K L : SSet.{0}} (f : K ⟶ L)
    (n : ℕ) (h : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).homology n) :
    HomologicalComplex.homologyMap (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := R) f) n
        (integralToScalarSimplicialHomology (R := R) K n h) =
      integralToScalarSimplicialHomology (R := R) L n
        (HomologicalComplex.homologyMap (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℤ) f) n h) := by
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K) n h
  rw [integralToScalarSimplicialHomology_chainClass, Cohomology.Singular.EvaluationNaturality.chainClass_naturality,
    Cohomology.Singular.EvaluationNaturality.chainClass_naturality, integralToScalarSimplicialHomology_chainClass,
    integralToScalarSimplicialCycles_naturality]

/-- Actual finite integral singular cycles with their scalar coefficients. -/
abbrev integralToScalarSingularCycles (X : TopCat.{0}) (n : ℕ) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n →ₗ[ℤ]
      Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) n :=
  integralToScalarSimplicialCycles (TopCat.toSSet.obj X) n

@[simp]
theorem integralToScalarSingularCycles_val (X : TopCat.{0}) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n) :
    (integralToScalarSingularCycles (R := R) X n z).val =
      IntegralCapCoefficients.integralToScalarSingular (R := R) X n z.val := rfl

/-- The native singular homology coefficient map, in particular from
integral homology to rational homology when `R = ℚ`. -/
abbrev integralToScalarSingularHomology (X : TopCat.{0}) (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n →ₗ[ℤ]
      (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n :=
  integralToScalarSimplicialHomology (TopCat.toSSet.obj X) n

@[simp]
theorem integralToScalarSingularHomology_chainClass (X : TopCat.{0}) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n) :
    integralToScalarSingularHomology (R := R) X n
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) n
        (integralToScalarSingularCycles (R := R) X n z) :=
  integralToScalarSimplicialHomology_chainClass (TopCat.toSSet.obj X) n z

theorem integralToScalarSingularCycles_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n) :
    Cohomology.Singular.EvaluationNaturality.chainCycleMap (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f) n
        (integralToScalarSingularCycles (R := R) X n z) =
      integralToScalarSingularCycles (R := R) Y n
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f) n z) :=
  integralToScalarSimplicialCycles_naturality (TopCat.toSSet.map f) n z

theorem integralToScalarSingularHomology_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (n : ℕ) (h : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n) :
    HomologicalComplex.homologyMap (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f) n
        (integralToScalarSingularHomology (R := R) X n h) =
      integralToScalarSingularHomology (R := R) Y n
        (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f) n h) :=
  integralToScalarSimplicialHomology_naturality (TopCat.toSSet.map f) n h

end

end OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients
