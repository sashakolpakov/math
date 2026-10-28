import OAI.Geometry.ComplexTorus.RiemannProjectivity.BettiDe
import Mathlib.RingTheory.Finiteness.Descent
import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas

/-! # Rational Loops -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.RationalLoops.Constructions.Rational

/-!
# RiemannProjectivity: the rational structure on the actual singular cohomology

Complex evaluation is linear over the complex numbers even when its
cycles have rational coefficients. Finite-dimensional complex cohomology
therefore forces finite-dimensional rational cohomology by faithful scalar
extension. This applies to the explicitly computed period torus.
-/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas

local instance (X : TopCat.{0}) (n : ℕ) :
    Module ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat.{0}) (n : ℕ) :
    IsScalarTower ℚ ℂ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

theorem evaluation_smul (X : TopCat.{0}) (n : ℕ) (a : ℂ)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n) :
    AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology X n (a • c) =
      a • AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology X n c := by
  let e := (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).toLinearEquiv
  have hi : e.symm (a • c) = AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap
      (ModuleCat.ofHom ((a • LinearMap.id : ℂ →ₗ[ℂ] ℂ).restrictScalars ℚ)) X n
        (e.symm c) := by
    apply e.injective
    exact (e.apply_symm_apply (a • c)).trans
      ((AlgebraicGeometry.ComplexMultiplication.Coefficient.CoefficientRestriction.CM.complexCohomologyRestrictionIso_scalar a X n (e.symm c)).trans
        (congrArg (a • ·) (e.apply_symm_apply c))).symm
  ext z
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℂ) X n (e.symm (a • c)) z = _
  rw [hi, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_coefficient]
  rfl

/-- Actual evaluation on rational cycles, bundled over the complex scalars. -/
def complexEvaluationEquiv (X : TopCat.{0}) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n ≃ₗ[ℂ]
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n →ₗ[ℚ] ℂ) :=
  LinearEquiv.ofBijective
    { toFun := AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology X n
      map_add' := (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology X n).map_add
      map_smul' := evaluation_smul X n }
    ((AlgebraicGeometry.ComplexMultiplication.Coefficient.Duality.CM.singularEvaluationWithCoefficientsEquiv (ModuleCat.of ℚ ℂ) X n).bijective.comp
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).toLinearEquiv.symm.bijective)

/-- Finiteness descends from complex cohomology without a finite-chain
assumption or a chosen rational comparison. -/
theorem rational_cohomology_finite (X : TopCat.{0}) (n : ℕ)
    [Module.Finite ℂ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n)] :
    Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n) := by
  let H := (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n
  let : Module.Finite ℂ (H →ₗ[ℚ] ℂ) :=
    Module.Finite.of_surjective (complexEvaluationEquiv X n).toLinearMap
      (complexEvaluationEquiv X n).surjective
  let : Module.Finite ℂ (Module.Dual ℂ (ℂ ⊗[ℚ] H)) :=
    Module.Finite.of_surjective (LinearMap.liftBaseChangeEquiv ℂ).toLinearMap
      (LinearMap.liftBaseChangeEquiv ℂ).surjective
  let : Module.Finite ℂ (ℂ ⊗[ℚ] H) := (Module.finite_dual_iff ℂ).mp inferInstance
  let : Module.Finite ℚ H := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat ℂ
  exact Module.Finite.of_surjective (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n).symm.toLinearMap
    (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n).symm.surjective

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)

theorem period_complex_h1_finite :
    Module.Finite ℂ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of Φ.periodTorus) 1) := by
  let : Module.Finite ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) :=
    Module.Finite.of_restrictScalars_finite ℝ ℂ _
  exact Module.Finite.of_surjective (BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ).toLinearMap
    (BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ).surjective

theorem period_rational_h1_finite :
    Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1) := by
  let := period_complex_h1_finite Φ
  exact rational_cohomology_finite (TopCat.of Φ.periodTorus) 1

/-- The actual coefficient inclusion complexifies to the computed covectors. -/
def rationalComplexificationCovectors :
    ℂ ⊗[ℚ] AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1 ≃ₗ[ℂ]
      (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) := by
  let := period_rational_h1_finite Φ
  exact (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (TopCat.of Φ.periodTorus) 1).trans
    (BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ).symm

end Geometry.ComplexTorus.RiemannProjectivity.RationalLoops.Constructions.Rational

namespace Geometry.ComplexTorus.RiemannProjectivity.RationalLoops.Constructions.Loops

/-! # RiemannProjectivity: explicit smooth lattice loops and their periods -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory _root_.MeasureTheory Set
open scoped Simplicial _root_.Manifold ContDiff

open OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)

def segmentMap (t : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) : C(Convexity.StdSimplex ℝ (Fin 2), Φ.periodTorus) where
  toFun x := QuotientAddGroup.mk (x.weights 1 • t)
  continuous_toFun := (FormsEq.Constructions.Forms.projection_real_smooth Φ).continuous.comp
    ((Convexity.StdSimplex.continuous_weights_apply ℝ (1 : Fin 2)).smul continuous_const)

def segmentSimplex (t : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus).toSSet _⦋1⦌ := by
  refine ⟨(TopCat.of Φ.periodTorus).toSSetObjEquiv _ |>.symm (segmentMap Φ t), ?_⟩
  change AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.IsManifoldSmoothSimplex (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (segmentMap Φ t)
  refine ⟨fun x : Fin 2 → ℝ => QuotientAddGroup.mk (x 1 • t), univ,
    isOpen_univ, subset_univ _, ?_, fun _ => rfl⟩
  exact ((FormsEq.Constructions.Forms.projection_real_smooth Φ).comp
    ((contDiff_apply (𝕜 := ℝ) (E := ℝ) 1).smul contDiff_const).contMDiff).contMDiffOn

@[simp]
theorem segmentSimplex_apply (t : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (x : Convexity.StdSimplex ℝ (Fin 2)) :
    (TopCat.of Φ.periodTorus).toSSetObjEquiv _ (segmentSimplex Φ t).val x =
      QuotientAddGroup.mk (x.weights 1 • t) := rfl

theorem latticeSegment_faces (t : Φ.periodIntegerLattice) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus).toSSet.δ 0
      (segmentSimplex Φ t) =
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus).toSSet.δ 1
      (segmentSimplex Φ t) := by
  apply Subtype.ext
  apply ((TopCat.of Φ.periodTorus).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro x
  change (TopCat.of Φ.periodTorus).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of Φ.periodTorus)).δ 0 (segmentSimplex Φ t).val) x =
    (TopCat.of Φ.periodTorus).toSSetObjEquiv _
      ((TopCat.toSSet.obj (TopCat.of Φ.periodTorus)).δ 1 (segmentSimplex Φ t).val) x
  rw [Subsingleton.elim x (Convexity.StdSimplex.single 0)]
  have h0 := TopCat.toSSetObjEquiv_δ_apply (segmentSimplex Φ t).val
    (0 : Fin 2) (Convexity.StdSimplex.single 0)
  have h1 := TopCat.toSSetObjEquiv_δ_apply (segmentSimplex Φ t).val
    (1 : Fin 2) (Convexity.StdSimplex.single 0)
  apply h0.trans
  apply Eq.trans _ h1.symm
  simp only [Convexity.StdSimplex.map_single]
  rw [segmentSimplex_apply, segmentSimplex_apply]
  simp only [Convexity.StdSimplex.weights_single]
  simp

/-- The straight lattice segment is an actual smooth singular cycle. -/
def latticeCycle (R : Type) [CommRing R] (t : Φ.periodIntegerLattice) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := R)
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus).toSSet) 1 := by
  refine ⟨AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain _ (segmentSimplex Φ t), ?_⟩
  rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ, AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain_boundary]
  simp [Fin.sum_univ_two, latticeSegment_faces Φ t]

def segmentCube (t : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :
    AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.SmoothManifoldCube (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) 1 where
  toFun u := (1 - u 0) • t
  smooth := ((contDiff_const.sub (contDiff_apply (𝕜 := ℝ) (E := ℝ) 0)).smul
    contDiff_const).contMDiff

theorem segmentCube_agrees (t : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (u : AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes.unitCube 1) :
    AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePostcompose (QuotientAddGroup.mk : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Φ.periodTorus)
      (FormsEq.Constructions.Forms.projection_real_smooth Φ) (segmentCube t) u.val =
    (TopCat.of Φ.periodTorus).toSSetObjEquiv _ (segmentSimplex Φ t).val
      (AlgebraicTopology.DeRham.Comparison.DuffyCoordinates.Duffy.toSimplex 1 u) := by
  rw [segmentSimplex_apply]
  change QuotientAddGroup.mk ((1 - u.val 0) • t) =
    (QuotientAddGroup.mk (AlgebraicTopology.DeRham.Comparison.DuffyCoordinates.Duffy.coordinates 1 u.val 1 • t) : Φ.periodTorus)
  simp [AlgebraicTopology.DeRham.Comparison.DuffyCoordinates.Duffy.coordinates]

theorem segmentCube_integrand (t : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ)
    (u : Fin 1 → ℝ) :
    AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePullback (segmentCube t)
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback
        (QuotientAddGroup.mk : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Φ.periodTorus)
        (FormsEq.Constructions.Forms.projection_real_smooth Φ)
        (FormsEq.Constructions.Forms.invariantForm Φ
          (ContinuousAlternatingMap.ofSubsingleton ℝ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) ℂ (0 : Fin 1) l)))
        u (fun j => Pi.single j 1) = -l t := by
  rw [AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePullback_apply]
  have hs : ContDiff ℝ ∞ (segmentCube t).toFun :=
    (contDiff_const.sub (contDiff_apply (𝕜 := ℝ) (E := ℝ) 0)).smul contDiff_const
  rw [AlgebraicTopology.DeRham.Comparison.NormedManifoldPullback.toNormedSpace_pullback_self (segmentCube t).toFun hs]
  rw [FormsEq.Constructions.Forms.invariantForm_pullback, Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback_apply_vectors]
  have hd : HasFDerivAt (fun u : Fin 1 → ℝ => (1 - u 0) • t)
      ((-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).smulRight t) u := by
    convert! ((hasFDerivAt_const (1 : ℝ) u).sub
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt).smul_const t
      using 1
    simp
  change l (fderiv ℝ (fun u : Fin 1 → ℝ => (1 - u 0) • t) u (Pi.single 0 1)) = _
  rw [hd.fderiv]
  simp

/-- The actual signed simplex integral along the segment equals its covector period. -/
theorem segment_integral (t : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) :
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration (segmentSimplex Φ t)
      (FormsEq.Constructions.Forms.invariantForm Φ
        (ContinuousAlternatingMap.ofSubsingleton ℝ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) ℂ (0 : Fin 1) l)) =
      l t := by
  rw [AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_eq_cube _ _ (segmentCube_agrees Φ t),
    AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubeIntegration_postcompose, AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubeIntegration_eq_integral]
  simp only [segmentCube_integrand, pow_one]
  simp [integral_const, Measure.real, Real.volume_Icc_pi]

/-- The represented loop in ordinary singular homology, with arbitrary scalar coefficients. -/
def latticeHomology (R : Type) [CommRing R] (t : Φ.periodIntegerLattice) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (TopCat.of Φ.periodTorus)).homology 1 :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := R)
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus) 1
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ 1 (latticeCycle Φ R t))

/-- The canonical Betti class pairs with a genuine lattice loop by its literal period. -/
theorem invariantBetti_period (t : Φ.periodIntegerLattice) (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of Φ.periodTorus) 1
      (BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ l) (latticeHomology Φ ℂ t) = l t := by
  change AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation _ (ModuleCat.of ℂ ℂ) 1 _
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := ℂ)
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus) 1 _) = _
  rw [← AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyEvaluation_naturality]
  change AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation _ (ModuleCat.of ℂ ℂ) 1
    ((AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1).hom
      (BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ l)) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ 1 (latticeCycle Φ ℂ t)) = _
  rw [BettiDe.Constructions.Betti.invariantBettiH1_restriction, AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class]
  change AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv _ (ModuleCat.of ℂ ℂ) 1
    (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1
      (FormsEq.Constructions.Forms.invariantClosedOneForm Φ l)).val
    (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain _ (segmentSimplex Φ t)) = _
  rw [AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex, AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle_evaluation]
  exact segment_integral Φ t l

end Geometry.ComplexTorus.RiemannProjectivity.RationalLoops.Constructions.Loops

namespace Geometry.ComplexTorus.RiemannProjectivity.RationalLoops.Constructions.Restriction

/-! # RiemannProjectivity: scalar restriction preserves actual representatives and periods -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

open OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas

variable {R S : Type} [CommRing R] [CommRing S]

abbrev restrictCochains (f : R →+* S) (C : CochainComplex (ModuleCat.{0} S) ℕ) :=
  ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C

/-- A cocycle of the restricted complex is literally the same cocycle. -/
def unrestrictedCocycle (f : R →+* S) (C : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (restrictCochains f C) n) : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles C n :=
  ⟨z.val, z.property⟩

/-- The native homology comparison for scalar restriction preserves representatives. -/
theorem restrictScalars_cochainClass (f : R →+* S)
    (C : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (restrictCochains f C) n) :
    ((C.sc n).mapHomologyIso (ModuleCat.restrictScalars f)).hom
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (restrictCochains f C) n z) =
        AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass C n (unrestrictedCocycle f C n z) := by
  let A := C.sc n
  let F := ModuleCat.restrictScalars f
  let d := A.moduleCatLeftHomologyData
  let k := ((restrictCochains f C).sc n).moduleCatCyclesIso.inv z
  have hk : (d.map F).cyclesIso.hom k = unrestrictedCocycle f C n z := by
    apply Subtype.ext
    have hi := ConcreteCategory.congr_hom ((d.map F).cyclesIso_hom_comp_i) k
    have hi' := ConcreteCategory.congr_hom
      (((restrictCochains f C).sc n).moduleCatCyclesIso_inv_iCycles) z
    exact hi.trans hi'
  rw [AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_homologyπ]
  change (A.mapHomologyIso F).hom ((A.map F).homologyπ k) = _
  rw [d.mapHomologyIso_eq F]
  change (F.map d.homologyIso.inv)
      ((d.map F).homologyIso.hom ((A.map F).homologyπ k)) = _
  have hp := ConcreteCategory.congr_hom
    ((d.map F).homologyπ_comp_homologyIso_hom) k
  calc
    _ = (F.map d.homologyIso.inv)
        ((d.map F).π ((d.map F).cyclesIso.hom k)) :=
      congrArg (fun q => (F.map d.homologyIso.inv) q) hp
    _ = (F.map d.homologyIso.inv)
        ((d.map F).π (unrestrictedCocycle f C n z)) :=
      congrArg (fun q => (F.map d.homologyIso.inv) ((d.map F).π q)) hk
    _ = _ := rfl

/-- The canonical product comparison leaves each simplex evaluation unchanged. -/
theorem restriction_evaluation (f : R →+* S) (K : SSet.{0}) (M : ModuleCat.{0} S)
    {n : ℕ} (s : K _⦋n⦌) :
    (AlgebraicTopology.Cohomology.Singular.Chains.simplicialCochainsRestrictScalarsIso f K M).hom.f n ≫
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K ((ModuleCat.restrictScalars f).obj M) s =
    (ModuleCat.restrictScalars f).map (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K M s) := by
  apply Quiver.Hom.op_inj
  change Sigma.ι (fun _ : K _⦋n⦌ => op ((ModuleCat.restrictScalars f).obj M)) s ≫
    sigmaComparison (ModuleCat.restrictScalars f).op (fun _ : K _⦋n⦌ => op M) =
      (ModuleCat.restrictScalars f).op.map (Sigma.ι (fun _ : K _⦋n⦌ => op M) s)
  exact ι_comp_sigmaComparison (ModuleCat.restrictScalars f).op (fun _ : K _⦋n⦌ => op M) s

/-- The actual cochain comparison from ordinary complex coefficients to
complex-valued rational coefficients. -/
def complexCochainRestriction (X : TopCat.{0}) :
    restrictCochains (algebraMap ℚ ℂ) (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) ⟶
      AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℂ) X :=
  (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X).hom ≫
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.inv X

def complexCocycleAsRational (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℂ) X) n :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (complexCochainRestriction X) n ⟨c.val, c.property⟩

theorem complexCocycleAsRational_evaluation (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) n)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℂ) s
      (complexCocycleAsRational X n c).val =
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) s c.val := by
  change AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation _ (ModuleCat.of ℚ ℂ) s
    ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.inv X).f n
      ((AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X).hom.f n c.val)) = _
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_evaluation AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.inv X s)
      ((AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X).hom.f n c.val)
  exact h.trans (ConcreteCategory.congr_hom
    (restriction_evaluation (algebraMap ℚ ℂ) (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) s) c.val)

theorem complexCocycleAsRational_class (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) n) :
    (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).hom
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (complexCocycleAsRational X n c)) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n c := by
  let C := AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X
  let cR : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (restrictCochains (algebraMap ℚ ℂ) C) n := ⟨c.val, c.property⟩
  have he : complexCochainRestriction X ≫
      AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom X ≫
        (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X).inv = 𝟙 _ := by
    simp only [complexCochainRestriction, Category.assoc]
    rw [← Category.assoc (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.inv X),
      ← AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_comp]
    simp
  change (((C.sc n).mapHomologyIso (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).hom)
    (HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X).inv n
        (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom X n
          (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (complexCochainRestriction X) n cR)))) = _
  rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  change ((C.sc n).mapHomologyIso (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).hom
    ((HomologicalComplex.homologyMap (complexCochainRestriction X) n ≫
      HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom X) n ≫
      HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X).inv n)
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n cR)) = _
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, he,
    HomologicalComplex.homologyMap_id]
  exact restrictScalars_cochainClass (algebraMap ℚ ℂ) C n cR

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)

/-- Evaluation on the same geometric loop is independent of whether its
scalar chain coefficient `1` is rational or complex. -/
theorem evaluation_lattice_coefficients
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of Φ.periodTorus) 1)
    (t : Φ.periodIntegerLattice) :
    AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (TopCat.of Φ.periodTorus) 1 c
      (Loops.latticeHomology Φ ℚ t) =
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of Φ.periodTorus) 1 c
      (Loops.latticeHomology Φ ℂ t) := by
  let X := TopCat.of Φ.periodTorus
  obtain ⟨a, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) 1 c
  have hi : (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X 1).inv (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 1 a) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 1 (complexCocycleAsRational X 1 a) := by
    have h := congrArg (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X 1).inv
      (complexCocycleAsRational_class X 1 a)
    exact h.symm.trans ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X 1).toLinearEquiv.symm_apply_apply _)
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℂ) X 1
    ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X 1).inv (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 1 a)) _ = _
  rw [hi]
  simp only [Loops.latticeHomology, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  change AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation _ (ModuleCat.of ℚ ℂ) 1
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 1 (complexCocycleAsRational X 1 a)) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ 1 _) =
    AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation _ (ModuleCat.of ℂ ℂ) 1
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 1 a) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ 1 _)
  rw [AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class, AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class]
  change AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv _ (ModuleCat.of ℚ ℂ) 1
    (complexCocycleAsRational X 1 a).val
    ((AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus)).f 1
      (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain _ (Loops.segmentSimplex Φ t))) =
    AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv _ (ModuleCat.of ℂ ℂ) 1 a.val
    ((AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus)).f 1
      (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain _ (Loops.segmentSimplex Φ t)))
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex,
    AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex, AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex]
  exact complexCocycleAsRational_evaluation X 1 a (Loops.segmentSimplex Φ t).val

/-- The computed period is the evaluation on an actual rational homology class. -/
theorem invariantBetti_rational_period (l : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ)
    (t : Φ.periodIntegerLattice) :
    AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (TopCat.of Φ.periodTorus) 1
      (BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ l) (Loops.latticeHomology Φ ℚ t) = l t := by
  rw [evaluation_lattice_coefficients, Loops.invariantBetti_period]

end Geometry.ComplexTorus.RiemannProjectivity.RationalLoops.Constructions.Restriction

namespace Geometry.ComplexTorus.RiemannProjectivity.RationalLoops.Constructions.Characters

/-!
# RiemannProjectivity: rational H¹ as rational lattice characters

The equivalence is evaluation on the actual lattice loops. Its inverse is
constructed from the proved invariant-form comparison and rational coefficient
retraction; injectivity then makes the resulting class independent of choices.
-/

open _root_.CategoryTheory

open OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)

local instance : Module ℚ
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of Φ.periodTorus) 1) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance : IsScalarTower ℚ ℂ
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of Φ.periodTorus) 1) :=
  IsScalarTower.of_compHom ℚ ℂ _

def rationalCovector :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1 →ₗ[ℚ]
      (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →L[ℝ] ℂ) :=
  ((BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ).symm.restrictScalars ℚ).toLinearMap.comp
    (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of Φ.periodTorus) 1).hom

theorem rationalCovector_period
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1)
    (t : Φ.periodIntegerLattice) :
    rationalCovector Φ c t =
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1 c
        (Loops.latticeHomology Φ ℚ t) : ℂ) := by
  have h := Restriction.invariantBetti_rational_period Φ (rationalCovector Φ c) t
  have he : BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ (rationalCovector Φ c) =
      AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of Φ.periodTorus) 1 c :=
    (BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ).apply_symm_apply _
  rw [he] at h
  have hp := AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology_smul_rational
    (TopCat.of Φ.periodTorus) 1 1 c (Loops.latticeHomology Φ ℚ t)
  simp only [one_smul, Algebra.smul_def, mul_one] at hp
  exact h.symm.trans hp

/-- Evaluation on loops is an additive rational-valued lattice character. -/
def rationalPeriodCharacter
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1) :
    Φ.periodIntegerLattice →ₗ[ℤ] ℚ where
  toFun t := AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1 c
    (Loops.latticeHomology Φ ℚ t)
  map_add' s t := by
    apply Rat.cast_injective (α := ℂ)
    rw [Rat.cast_add, ← rationalCovector_period, ← rationalCovector_period,
      ← rationalCovector_period]
    exact (rationalCovector Φ c).map_add s t
  map_smul' n t := by
    apply Rat.cast_injective (α := ℂ)
    change (_ : ℂ) = ((n • (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ)
      (TopCat.of Φ.periodTorus) 1 c (Loops.latticeHomology Φ ℚ t)) : ℚ) : ℂ)
    rw [show ∀ q : ℚ, ((n • q : ℚ) : ℂ) = n • (q : ℂ) from
      fun q => map_zsmul (algebraMap ℚ ℂ) n q,
      ← rationalCovector_period, ← rationalCovector_period]
    exact map_zsmul (rationalCovector Φ c) n t.val

def rationalPeriodMap :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1 →ₗ[ℚ]
      (Φ.periodIntegerLattice →ₗ[ℤ] ℚ) where
  toFun := rationalPeriodCharacter Φ
  map_add' c d := by
    ext t
    exact LinearMap.congr_fun (map_add
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1) c d) _
  map_smul' a c := by
    ext t
    exact LinearMap.congr_fun (map_smul
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1) a c) _

theorem rationalPeriodMap_injective : Function.Injective (rationalPeriodMap Φ) := by
  intro c d h
  apply AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology_injective (TopCat.of Φ.periodTorus) 1
  apply (BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ).symm.injective
  change rationalCovector Φ c = rationalCovector Φ d
  let χ : Φ.periodIntegerLattice →+ ℂ :=
    (rationalCovector Φ c).toLinearMap.toAddMonoidHom.comp
      Φ.periodIntegerLattice.subtype.toAddMonoidHom
  have hc : ∀ t : Φ.periodIntegerLattice, rationalCovector Φ c t = χ t := fun _ => rfl
  have hd : ∀ t : Φ.periodIntegerLattice, rationalCovector Φ d t = χ t := by
    intro t
    change rationalCovector Φ d t = rationalCovector Φ c t
    rw [rationalCovector_period, rationalCovector_period]
    exact congrArg (fun q : ℚ => (q : ℂ)) (LinearMap.congr_fun h t).symm
  exact (PrimitiveEq.Constructions.Primitive.exists_covector_extending_character Φ.periodIntegerLattice χ).unique hc hd

theorem rationalPeriodMap_surjective : Function.Surjective (rationalPeriodMap Φ) := by
  intro χ
  let χC : Φ.periodIntegerLattice →+ ℂ :=
    AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion.toAddMonoidHom.comp χ.toAddMonoidHom
  obtain ⟨l, hl, _⟩ := PrimitiveEq.Constructions.Primitive.exists_covector_extending_character Φ.periodIntegerLattice χC
  let c := BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ l
  refine ⟨AlgebraicTopology.Cohomology.Singular.RationalComplex.complexToRationalCohomology (TopCat.of Φ.periodTorus) 1 c, ?_⟩
  apply LinearMap.ext
  intro t
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1
    (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalRetraction) (TopCat.of Φ.periodTorus) 1
      ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso (TopCat.of Φ.periodTorus) 1).inv c))
    (Loops.latticeHomology Φ ℚ t) = χ t
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_coefficient]
  change AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalRetraction
    (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (TopCat.of Φ.periodTorus) 1 c
      (Loops.latticeHomology Φ ℚ t)) = χ t
  rw [Restriction.invariantBetti_rational_period, hl]
  exact LinearMap.congr_fun AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalRetraction_comp_inclusion (χ t)

/-- Rational H¹ is precisely the rational-valued characters on the full lattice. -/
def rationalPeriodEquiv :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Φ.periodTorus) 1 ≃ₗ[ℚ]
      (Φ.periodIntegerLattice →ₗ[ℤ] ℚ) :=
  LinearEquiv.ofBijective (rationalPeriodMap Φ)
    ⟨rationalPeriodMap_injective Φ, rationalPeriodMap_surjective Φ⟩

end Geometry.ComplexTorus.RiemannProjectivity.RationalLoops.Constructions.Characters

end

end OAI
