import OAI.AlgebraicTopology.Cohomology.Singular.Evaluation
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient

/-! # Evaluation Naturality -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

noncomputable section

/-!
# Naturality of the canonical singular evaluation pairing

The chain maps below are mathlib's actual simplicial and singular chain maps.
Evaluation commutes with pullback in cohomology, pushforward in homology, and
maps of coefficient modules. The field universal-coefficient isomorphism has
the same naturality because its forward map is this canonical evaluation.
-/

open _root_.CategoryTheory
open scoped Simplicial

variable {R : Type} [CommRing R]
variable {C D : ChainComplex (ModuleCat.{0} R) ℕ}

/-- Restriction of an actual chain map to the cycle submodules. -/
def chainCycleMap (f : C ⟶ D) (n : ℕ) : ChainRepresentatives.chainCycles C n →ₗ[R] ChainRepresentatives.chainCycles D n :=
  ((f.f n).hom.comp (ChainRepresentatives.chainCycles C n).subtype).codRestrict _ fun z => by
    change (D.d n ((ComplexShape.down ℕ).next n)) ((f.f n) (z : C.X n)) = 0
    have h := ConcreteCategory.congr_hom (f.comm n ((ComplexShape.down ℕ).next n))
      (z : C.X n)
    simpa only [ConcreteCategory.comp_apply,
      ChainRepresentatives.chainCycle_d_eq_zero C n ((ComplexShape.down ℕ).next n) z, map_zero] using h

@[simp]
theorem chainCycleMap_val (f : C ⟶ D) (n : ℕ) (z : ChainRepresentatives.chainCycles C n) :
    (chainCycleMap f n z : D.X n) = (f.f n) (z : C.X n) := rfl

/-- The concrete cycle map is the categorical cycle map in concrete coordinates. -/
theorem chainCycleMap_eq_cyclesMap (f : C ⟶ D) (n : ℕ) (z : ChainRepresentatives.chainCycles C n) :
    (D.sc n).moduleCatCyclesIso.inv (chainCycleMap f n z) =
      (HomologicalComplex.cyclesMap f n) ((C.sc n).moduleCatCyclesIso.inv z) := by
  apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
  have hD := ConcreteCategory.congr_hom ((D.sc n).moduleCatCyclesIso_inv_iCycles)
    (chainCycleMap f n z)
  have hC := ConcreteCategory.congr_hom ((C.sc n).moduleCatCyclesIso_inv_iCycles) z
  have hf := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n)
    ((C.sc n).moduleCatCyclesIso.inv z)
  change (D.iCycles n) ((D.sc n).moduleCatCyclesIso.inv (chainCycleMap f n z)) =
    (f.f n) (z : C.X n) at hD
  change (C.iCycles n) ((C.sc n).moduleCatCyclesIso.inv z) = (z : C.X n) at hC
  change (D.iCycles n) ((HomologicalComplex.cyclesMap f n)
    ((C.sc n).moduleCatCyclesIso.inv z)) =
      (f.f n) ((C.iCycles n) ((C.sc n).moduleCatCyclesIso.inv z)) at hf
  rw [hC] at hf
  exact hD.trans hf.symm

/-- An actual chain map sends a represented homology class to the image cycle's class. -/
theorem chainClass_naturality (f : C ⟶ D) (n : ℕ) (z : ChainRepresentatives.chainCycles C n) :
    (HomologicalComplex.homologyMap f n) (ChainRepresentatives.chainClass C n z) =
      ChainRepresentatives.chainClass D n (chainCycleMap f n z) := by
  rw [ChainRepresentatives.chainClass_eq_homologyπ, ChainRepresentatives.chainClass_eq_homologyπ, chainCycleMap_eq_cyclesMap]
  exact ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n)
    ((C.sc n).moduleCatCyclesIso.inv z)

/-- A chain map sends a boundary representative to the boundary of its image. -/
theorem chainCycleMap_boundary (f : C ⟶ D) (n : ℕ) (z : (C.sc n).X₁) :
    chainCycleMap f n (ChainRepresentatives.chainBoundaryMap C n z) =
      ChainRepresentatives.chainBoundaryMap D n ((f.f ((ComplexShape.down ℕ).prev n)) z) := by
  apply Subtype.ext
  exact (ConcreteCategory.congr_hom (f.comm ((ComplexShape.down ℕ).prev n) n) z).symm

/-- The actual scalar chain map of a morphism of simplicial sets. -/
abbrev simplicialScalarChainMap {K L : SSet.{0}} (f : K ⟶ L) :
    ChainDual.simplicialScalarChains (R := R) K ⟶ ChainDual.simplicialScalarChains (R := R) L :=
  SSet.chainComplexMap f (ModuleCat.of R R)

/-- The actual pushforward on scalar simplicial homology. -/
abbrev simplicialHomologyPushforward {K L : SSet.{0}} (f : K ⟶ L) (n : ℕ) :
    (ChainDual.simplicialScalarChains (R := R) K).homology n ⟶
      (ChainDual.simplicialScalarChains (R := R) L).homology n :=
  HomologicalComplex.homologyMap (simplicialScalarChainMap (R := R) f) n

@[simp]
theorem simplicialScalarChainMap_simplex {K L : SSet.{0}} (f : K ⟶ L)
    {n : ℕ} (s : K _⦋n⦌) :
    (simplicialScalarChainMap (R := R) f).f n (ChainDual.simplexChain K s) =
      ChainDual.simplexChain L (f.app _ s) :=
  ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f (X := K) (Y := L) (R := ModuleCat.of R R) f s) 1

/-- Pullback of an actual cochain is precomposition with the actual scalar chain map. -/
theorem degreewiseChainDualEquiv_pullback (M : ModuleCat.{0} R)
    {K L : SSet.{0}} (f : K ⟶ L) (n : ℕ) (c : (Basic.simplicialCochains L M).X n) :
    ChainDual.degreewiseChainDualEquiv K M n ((Functor.simplicialPullback M f).f n c) =
      (ChainDual.degreewiseChainDualEquiv L M n c).comp
        ((simplicialScalarChainMap (R := R) f).f n).hom := by
  apply ChainDual.chainFunctional_ext K M
  intro s
  simp only [ChainDual.degreewiseChainDualEquiv_simplex, LinearMap.comp_apply,
    simplicialScalarChainMap_simplex, Formulas.evaluation_pullback_apply]

/-- The canonical simplicial pairing is natural in the underlying simplicial set. -/
theorem simplicialHomologyEvaluation_naturality (M : ModuleCat.{0} R)
    {K L : SSet.{0}} (f : K ⟶ L) (n : ℕ)
    (c : (Basic.simplicialCochains L M).homology n)
    (z : (ChainDual.simplicialScalarChains (R := R) K).homology n) :
    Evaluation.simplicialHomologyEvaluation K M n
        ((HomologicalComplex.homologyMap (Functor.simplicialPullback M f) n) c) z =
      Evaluation.simplicialHomologyEvaluation L M n c
        (simplicialHomologyPushforward (R := R) f n z) := by
  obtain ⟨c, rfl⟩ := Representatives.cochainClass_surjective (Basic.simplicialCochains L M) n c
  obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (ChainDual.simplicialScalarChains (R := R) K) n z
  rw [RepresentativesNaturality.cochainClass_naturality, chainClass_naturality,
    Evaluation.simplicialHomologyEvaluation_class_class, Evaluation.simplicialHomologyEvaluation_class_class]
  exact LinearMap.congr_fun (degreewiseChainDualEquiv_pullback M f n c.val) z.val

/-- The actual scalar singular chain map of a continuous map. -/
abbrev singularScalarChainMap {X Y : TopCat.{0}} (f : X ⟶ Y) :
    Evaluation.singularScalarChains (R := R) X ⟶ Evaluation.singularScalarChains (R := R) Y :=
  simplicialScalarChainMap (R := R) (TopCat.toSSet.map f)

/-- Pushforward of actual scalar singular homology classes. -/
abbrev singularHomologyPushforward {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (Evaluation.singularScalarChains (R := R) X).homology n ⟶
      (Evaluation.singularScalarChains (R := R) Y).homology n :=
  simplicialHomologyPushforward (R := R) (TopCat.toSSet.map f) n

/-- The chain representative formula for continuous pushforward in homology. -/
theorem singularHomologyPushforward_class {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (z : ChainRepresentatives.chainCycles (Evaluation.singularScalarChains (R := R) X) n) :
    singularHomologyPushforward (R := R) f n (ChainRepresentatives.chainClass (Evaluation.singularScalarChains X) n z) =
      ChainRepresentatives.chainClass (Evaluation.singularScalarChains Y) n
        (chainCycleMap (singularScalarChainMap (R := R) f) n z) :=
  chainClass_naturality (singularScalarChainMap (R := R) f) n z

/-- Pullback in singular cohomology is adjoint to continuous pushforward in homology. -/
theorem singularEvaluation_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : Basic.singularCohomology M Y n) (z : (Evaluation.singularScalarChains (R := R) X).homology n) :
    Evaluation.singularEvaluation M X n ((Functor.singularCohomologyPullback M f n) c) z =
      Evaluation.singularEvaluation M Y n c (singularHomologyPushforward (R := R) f n z) :=
  simplicialHomologyEvaluation_naturality M (TopCat.toSSet.map f) n c z

/-- On singular cochains, changing coefficients postcomposes the chain functional. -/
theorem singularDegreewiseChainDualEquiv_coefficient {M N : ModuleCat.{0} R}
    (f : M ⟶ N) (X : TopCat.{0}) (n : ℕ) (c : (Basic.singularCochains M X).X n) :
    ChainDual.singularDegreewiseChainDualEquiv N X n ((Coefficients.coefficientCochainMap f X).f n c) =
      f.hom.comp (ChainDual.singularDegreewiseChainDualEquiv M X n c) := by
  apply ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) N
  intro s
  change ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) N n
      ((Coefficients.coefficientCochainMap f X).f n c) (ChainDual.simplexChain (TopCat.toSSet.obj X) s) =
    f (ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) M n c
      (ChainDual.simplexChain (TopCat.toSSet.obj X) s))
  rw [ChainDual.degreewiseChainDualEquiv_simplex, ChainDual.degreewiseChainDualEquiv_simplex]
  exact ConcreteCategory.congr_hom (Coefficients.coefficientCochainMap_evaluation f X s) c

/-- The canonical singular pairing is natural in its coefficient module. -/
theorem singularEvaluation_coefficient {M N : ModuleCat.{0} R}
    (f : M ⟶ N) (X : TopCat.{0}) (n : ℕ)
    (c : Basic.singularCohomology M X n) (z : (Evaluation.singularScalarChains (R := R) X).homology n) :
    Evaluation.singularEvaluation N X n ((Coefficients.coefficientMap f X n) c) z =
      f (Evaluation.singularEvaluation M X n c z) := by
  obtain ⟨c, rfl⟩ := Representatives.singularClass_surjective M X n c
  obtain ⟨z, rfl⟩ := ChainRepresentatives.chainClass_surjective (Evaluation.singularScalarChains (R := R) X) n z
  rw [RepresentativesNaturality.coefficientMap_class, Evaluation.singularEvaluation_class_class, Evaluation.singularEvaluation_class_class]
  exact LinearMap.congr_fun (singularDegreewiseChainDualEquiv_coefficient f X n c.val) z.val

variable {F : Type} [Field F]

/-- The field universal-coefficient identification is contravariantly natural. -/
theorem singularUniversalCoefficientEquiv_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (c : Basic.singularCohomology (ModuleCat.of F F) Y n) :
    UniversalCoefficient.singularUniversalCoefficientEquiv X n
        ((Functor.singularCohomologyPullback (ModuleCat.of F F) f n) c) =
      (UniversalCoefficient.singularUniversalCoefficientEquiv Y n c).comp
        (singularHomologyPushforward (R := F) f n).hom := by
  ext z
  simp only [UniversalCoefficient.singularUniversalCoefficientEquiv_apply, LinearMap.comp_apply]
  exact singularEvaluation_naturality (ModuleCat.of F F) f n c z

end

end OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
