import OAI.AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity
import OAI.AlgebraicTopology.Duality.Poincare.RationalizedChainClasses

/-! # Relative Rational Evaluation Comparison -/

namespace OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison

noncomputable section

/-!
# Integral and rational evaluation of relative rational cohomology

The rational relative-chain universal-coefficient pairing agrees with the
pairing on integral relative homology after extension of scalars. In
particular, the normalized complex normal class evaluates to one on the
specified integral orientation generator.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial TensorProduct ChangeOfRings

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Rational and integral chain functionals evaluate identically on an
integral chain with its coefficient changed to one in the tensor factor. -/
theorem singularRationalEvaluation_one_tmul (X : TopCat.{0}) (n : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X n c
        ((AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n
          ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z)) =
      RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) n c z := by
  let f : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] RelativeCochainDual.rationalIntegralCoefficient :=
    ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom ℚ)).homEquiv _ _
      ((AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n ≫
        ModuleCat.ofHom (Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X n c))).hom
  have hf : f = RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) n c := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) RelativeCochainDual.rationalIntegralCoefficient
    intro σ
    change Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X n c
        ((AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n
          ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
            (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ 1)) = _
    rw [AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_one_tmul_simplex]
    exact (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex (TopCat.toSSet.obj X)
      (ModuleCat.of ℚ ℚ) c σ).trans
        (RelativeCochainDual.rationalSimplicialChainDualEquiv_simplex (TopCat.toSSet.obj X) n c σ).symm
  exact LinearMap.congr_fun hf z

/-- The actual relative coefficient-change isomorphism carries a projected
integral chain to the projection of the coefficient-changed absolute chain. -/
theorem rationalRelativeChainsIso_one_tmul_projection (X : TopCat.{0})
    (A : Set X) (n : ℕ) (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A).hom.f n
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n z)) =
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A).f n
        ((AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n
          ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z)) := by
  have hn : (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A)).f n ≫
        (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A).hom.f n =
      (AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).hom.f n ≫ (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A).f n :=
    congrArg (fun f : AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) ⟶
      AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A => f.f n) (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso_projection X A)
  have h := ConcreteCategory.congr_hom hn
    (show (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X)).X n from
      (1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z)
  exact h

/-- The two actual relative cochain functionals agree after the actual
rationalization isomorphism, on every integral relative chain. -/
theorem relativeRationalEvaluation_one_tmul (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X n)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X n) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X A n c
        ((AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A).hom.f n
          ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z)) =
      RelativeCochainDual.relativeCochainIntegralDualEquiv X A n c z := by
  have hs : Function.Surjective ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n) :=
    AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective ℤ X A n
  obtain ⟨z, rfl⟩ := hs z
  rw [rationalRelativeChainsIso_one_tmul_projection,
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv_projection,
    RelativeCochainDual.relativeCochainIntegralDualEquiv_projection]
  exact singularRationalEvaluation_one_tmul X n
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n c) z

/-- Under the actual relative rationalization isomorphism, the class of a
coefficient-changed relative cycle is the tensor of its integral class. -/
theorem rationalRelativeHomologyIso_chainClass (X : TopCat.{0}) (A : Set X)
    (n : ℕ) (q : ℚ) (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).hom
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) n
          (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A).hom n
            (RationalizedChainClasses.Cycles.rationalizedChainCycle (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n q z))) =
      q ⊗ₜ[ℤ, Int.castRingHom ℚ] (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n z) := by
  rw [← Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  let e := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ)
    (ComplexShape.down ℕ) n).mapIso (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A)
  change (AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeHomologyIso (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n).hom
    (e.inv (e.hom (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalizeChains.obj (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A)) n
      (RationalizedChainClasses.Cycles.rationalizedChainCycle (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n q z)))) = _
  rw [Iso.hom_inv_id_apply]
  exact RationalizedChainClasses.Cycles.rationalizeHomologyIso_chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n q z

/-- The integral-homology and rational-homology evaluation pairings agree
under the actual coefficient-change isomorphism, for every topological pair. -/
theorem relativeRationalHomologyEvaluation_eq_scalarEvaluation
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A n) :
    RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X A n c z =
      AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n c
        ((AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).inv
          ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z)) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) n c
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n z
  have hz : (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).inv
        ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n z)) =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) n
        (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso X A).hom n
          (RationalizedChainClasses.Cycles.rationalizedChainCycle (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n 1 z)) := by
    apply (ModuleCat.mono_iff_injective (AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).hom).mp
      inferInstance
    rw [Iso.inv_hom_id_apply, rationalRelativeHomologyIso_chainClass]
  rw [hz, RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_class_class,
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv_class_class]
  exact (relativeRationalEvaluation_one_tmul X A n c.val z.val).symm

/-- The normalized rational normal class evaluates to one on the specified
integral complex-orientation generator, including in complex dimension zero. -/
theorem complexNormalRationalDualClass_integralEvaluation (p : ℕ) :
    RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of (Fin p → ℂ))
      ({0}ᶜ : Set (Fin p → ℂ)) (2 * p) (AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
        ((AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1) = 1 := by
  rw [relativeRationalHomologyEvaluation_eq_scalarEvaluation,
    AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_functional]
  change AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso.hom
    (AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map (AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).hom
      ((AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso (TopCat.of (Fin p → ℂ))
        ({0}ᶜ : Set (Fin p → ℂ)) (2 * p)).hom
        ((AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso (TopCat.of (Fin p → ℂ))
          ({0}ᶜ : Set (Fin p → ℂ)) (2 * p)).inv
          ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
            ((AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1))))) = 1
  rw [Iso.inv_hom_id_apply]
  change AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso.hom
    ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
      ((AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).hom
        ((AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).inv 1))) = 1
  rw [Iso.inv_hom_id_apply]
  exact AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso_hom_one_tmul 1

end

end OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison
