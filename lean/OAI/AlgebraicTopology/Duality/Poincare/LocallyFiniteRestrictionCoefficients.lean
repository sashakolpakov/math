import OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCoefficientHomology
import OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction

/-! # Locally Finite Restriction Coefficients -/

namespace OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteRestrictionCoefficients

noncomputable section

/-!
# Coefficient change and compact restriction of locally finite chains

Integer-to-rational coefficient change commutes with the actual finite
truncation near a compact subset and hence with its relative quotient.
The final homology formula uses the established rationalization comparison
of genuine relative singular homology, with coefficient map `z ↦ 1 ⊗ z`.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial TensorProduct ChangeOfRings

open OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The established scalar-extension comparison agrees with the finite
coefficient-change map on every integral singular chain. -/
theorem rationalSingularChainsIso_one_tmul_eq_integralToScalar
    (X : TopCat.{0}) (n : ℕ) (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    (AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] c) =
      IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n c := by
  have he :
      ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom ℚ)).homEquiv _ _
        ((AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n)).hom =
      ((IntegralCapCoefficients.integralToScalarSingularChainMap (R := ℚ) X).f n).hom := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X)
      ((ModuleCat.restrictScalars (Int.castRingHom ℚ)).obj
        ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X n))
    intro σ
    change (AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
          (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) σ)) =
      IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n
        (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) σ)
    exact (AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_one_tmul_simplex X n σ).trans
      (IntegralCapCoefficients.integralToScalarSimplicial_simplex (R := ℚ) (TopCat.toSSet.obj X) n σ).symm
  exact LinearMap.congr_fun he c

/-- The ordinary finite-chain coefficient map is literal coefficient casting. -/
theorem ordinarySingularChainCoefficients_integralToRational
    (X : TopCat.{0}) (n : ℕ) (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℚ X n
        (IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n c) σ =
      (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n c σ : ℚ) := by
  exact (congrArg (fun z : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℚ X n => z σ)
    (LocallyFiniteCoefficients.locallyFiniteIntegralToRational_ordinary X n c)).symm

/-- Rational coefficient change commutes with the actual finite truncation
retaining the simplices that meet the compact set. -/
theorem locallyFiniteIntegralToRational_compactTruncation
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (n : ℕ)
    (c : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n) :
    IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation X K hK n c) =
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactTruncation ℚ X K hK n
        (LocallyFiniteCoefficients.locallyFiniteIntegralToRational X n c) := by
  classical
  apply (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℚ X n).injective
  apply Finsupp.ext
  intro σ
  rw [ordinarySingularChainCoefficients_integralToRational,
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation_coefficients,
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactTruncation_coefficients]
  by_cases hσ : (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ K).Nonempty
  · simp only [ite_eq_left hσ, LocallyFiniteCoefficients.locallyFiniteIntegralToRational_apply]
  · simp only [ite_eq_right hσ, Int.cast_zero]

/-- The existing relative coefficient comparison, viewed as a map from
integral chains to the same rational chains with integer scalars. -/
def integralToRationalRelativeChainMap (X : TopCat.{0}) (A : Set X) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A ⟶
      LocallyFiniteCoefficientHomology.restrictRationalChainComplex (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) where
  f n := (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom ℚ)).homEquiv _ _
    ((AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A).hom.f n)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact ConcreteCategory.congr_hom ((AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A).hom.comm i j)
      ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] c)

@[simp]
theorem integralToRationalRelativeChainMap_f_apply
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X n) :
    (integralToRationalRelativeChainMap X A).f n c =
      (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A).hom.f n
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] c) := rfl

/-- The relative coefficient map is induced by the actual finite coefficient
map before passing to the subspace quotient. -/
theorem integralToRationalRelativeChainMap_projection
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    (integralToRationalRelativeChainMap X A).f n
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n c) =
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A).f n
        (IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n c) := by
  rw [integralToRationalRelativeChainMap_f_apply,
    RelativeRationalEvaluationComparison.rationalRelativeChainsIso_one_tmul_projection,
    rationalSingularChainsIso_one_tmul_eq_integralToScalar]

/-- Coefficient change commutes with compact-relative restriction in every degree. -/
theorem locallyFiniteIntegralToRational_compactRestrictionDegree
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (n : ℕ)
    (c : AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestrictionDegree ℚ X K hK n
        (LocallyFiniteCoefficients.locallyFiniteIntegralToRational X n c) =
      (integralToRationalRelativeChainMap X Kᶜ).f n
        (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestrictionDegree X K hK n c) := by
  change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X Kᶜ).f n
      (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactTruncation ℚ X K hK n
        (LocallyFiniteCoefficients.locallyFiniteIntegralToRational X n c)) =
    (integralToRationalRelativeChainMap X Kᶜ).f n
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ).f n (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation X K hK n c))
  rw [integralToRationalRelativeChainMap_projection,
    locallyFiniteIntegralToRational_compactTruncation]

/-- The compact restriction square is a square of the genuine chain maps. -/
@[reassoc]
theorem locallyFiniteIntegralToRationalChainMap_compactRestriction
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) :
    LocallyFiniteCoefficients.locallyFiniteIntegralToRationalChainMap X ≫
        ((ModuleCat.restrictScalars (Int.castRingHom ℚ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestriction ℚ X K hK) =
      AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X K hK ≫ integralToRationalRelativeChainMap X Kᶜ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact locallyFiniteIntegralToRational_compactRestrictionDegree X K hK n c

/-- The relative coefficient chain map keeps the actual rationalized cycle,
including its fixed unit tensor coefficient. -/
theorem integralToRationalRelativeChainMap_cycle
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    LocallyFiniteCoefficientHomology.rationalCycleOfRestricted (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) n
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (integralToRationalRelativeChainMap X A) n z) =
      Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A).hom n
        (RationalizedChainClasses.Cycles.rationalizedChainCycle (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n 1 z) := by
  apply Subtype.ext
  rfl

/-- On native homology the relative coefficient map is precisely the
established scalar-extension map `h ↦ 1 ⊗ h`. -/
theorem integralToRationalRelativeChainMap_homology
    (X : TopCat.{0}) (A : Set X) (n : ℕ) (h : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A n) :
    (LocallyFiniteCoefficientHomology.rationalChainHomologyRestrictIso (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) n).hom
        (HomologicalComplex.homologyMap (integralToRationalRelativeChainMap X A) n h) =
      (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).inv
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] h) := by
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n h
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality, LocallyFiniteCoefficientHomology.rationalChainHomologyRestrictIso_chainClass,
    integralToRationalRelativeChainMap_cycle]
  apply (ModuleCat.mono_iff_injective (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).hom).mp
    inferInstance
  rw [Iso.inv_hom_id_apply, RelativeRationalEvaluationComparison.rationalRelativeHomologyIso_chainClass]

/-- Compact restriction of a rationalized locally finite cycle is the
rationalized compact restriction of the original cycle. -/
theorem locallyFiniteIntegralToRationalCycles_compactRestriction
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) n) :
    Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestriction ℚ X K hK) n
        (LocallyFiniteCoefficientHomology.locallyFiniteIntegralToRationalCycles X n z) =
      LocallyFiniteCoefficientHomology.rationalCycleOfRestricted (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X Kᶜ) n
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (integralToRationalRelativeChainMap X Kᶜ) n
          (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X K hK) n z)) := by
  apply Subtype.ext
  exact locallyFiniteIntegralToRational_compactRestrictionDegree X K hK n z.val

/-- On the native homology groups, changing coefficients and restricting near
a compact set commute. The right side is the already normalized relative
rationalization comparison, not an unspecified coefficient isomorphism. -/
theorem locallyFiniteIntegralToRationalHomology_compactRestriction
    (X : TopCat.{0}) (K : Set X) (hK : IsCompact K) (n : ℕ)
    (h : (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n) :
    AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactHomologyRestriction ℚ X K hK n
        (LocallyFiniteCoefficients.locallyFiniteIntegralToRationalHomology X n h) =
      (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X Kᶜ n).inv
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
          (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X K hK n h)) := by
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X) n h
  rw [LocallyFiniteCoefficientHomology.locallyFiniteIntegralToRationalHomology_chainClass]
  change HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteScalarRestriction.Cycles.locallyFiniteScalarCompactRestriction ℚ X K hK) n
      (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℚ X) n
        (LocallyFiniteCoefficientHomology.locallyFiniteIntegralToRationalCycles X n z)) = _
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality, locallyFiniteIntegralToRationalCycles_compactRestriction,
    integralToRationalRelativeChainMap_cycle]
  apply (ModuleCat.mono_iff_injective (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X Kᶜ n).hom).mp
    inferInstance
  rw [Iso.inv_hom_id_apply, RelativeRationalEvaluationComparison.rationalRelativeHomologyIso_chainClass]
  congr 1
  exact (Cohomology.Singular.EvaluationNaturality.chainClass_naturality (AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X K hK) n z).symm

end

end OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteRestrictionCoefficients
