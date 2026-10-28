import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Naturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PeriodEdges
import OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients
import OAI.AlgebraicTopology.Kunneth.ComparisonLow
import OAI.AlgebraicTopology.Products.CupCohomology
import Mathlib.Tactic.FinCases

/-! # Loop -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.Loop

noncomputable section

section

/-! Original integral periods give literal singular one-cycles. Their
rational classes are the native homology marking, as detected by every H¹ class. -/

open _root_.CategoryTheory Opposite
open scoped Simplicial

open OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Λ : Submodule ℤ V)

def latticePeriodLoop (ℓ : Λ) : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 :=
  (TopCat.toSSet.map (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ)).app (op ⦋1⦌) (HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge (ℓ : V))

theorem latticePeriodLoop_closed (ℓ : Λ) :
    (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).δ 0 (latticePeriodLoop Λ ℓ) =
      (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).δ 1 (latticePeriodLoop Λ ℓ) := by
  apply TopCat.toSSetObj₀Equiv.injective
  erw [← TopCat.toSSetObj₁Equiv_apply_one, ← TopCat.toSSetObj₁Equiv_apply_zero]
  have he (t : TopCat.I) : TopCat.toSSetObj₁Equiv (latticePeriodLoop Λ ℓ) t =
      HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection Λ (TopCat.toSSetObj₁Equiv (HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge (ℓ : V)) t) := rfl
  rw [he, he, HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge_one, HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge_zero]
  change (QuotientAddGroup.mk (ℓ : V) : V ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk 0
  rw [(QuotientAddGroup.eq_zero_iff (ℓ : V)).mpr ℓ.property]
  rfl

def latticePeriodLoopCycle (R : Type) [CommRing R] (ℓ : Λ) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) 1 :=
  ⟨AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) (latticePeriodLoop Λ ℓ), by
    apply (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) 0 _).mpr
    let K := TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)
    let p := latticePeriodLoop Λ ℓ
    let f : Fin 2 → (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X 0 :=
      fun i => ((-1 : ℤ) ^ i.val) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ i p)
    have h0 : f 0 = AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 0 p) := by
      change (1 : ℤ) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 0 p) = _
      exact one_zsmul _
    have h1 : f 1 = -AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 1 p) := by
      change (-1 : ℤ) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 1 p) = _
      exact neg_one_zsmul _
    have he : AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 0 p) =
        AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 1 p) :=
      congrArg (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K) (latticePeriodLoop_closed Λ ℓ)
    have hz : f 0 + f 1 = 0 :=
      (congrArg₂ (fun a b : (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K).X 0 => a + b) h0 h1).trans
        ((congrArg (fun a => a + -AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 1 p)) he).trans
          (add_neg_cancel _))
    exact (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain_boundary (R := R) K (n := 0) p).trans
      ((Fin.sum_univ_two f).trans hz)⟩

def latticePeriodLoopHomology (R : Type) [CommRing R] (ℓ : Λ) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)).homology 1 :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) 1 (latticePeriodLoopCycle Λ R ℓ)

theorem latticePeriodLoopHomology_rationalize (ℓ : Λ) :
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1
        (latticePeriodLoopHomology Λ ℤ ℓ) = latticePeriodLoopHomology Λ ℚ ℓ := by
  let zI : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) 1 :=
    latticePeriodLoopCycle Λ ℤ ℓ
  have h := AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology_chainClass (R := ℚ) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 zI
  have hz : AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 zI =
      latticePeriodLoopCycle Λ ℚ ℓ := by
    apply Subtype.ext
    exact AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial_simplex (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) 1 (latticePeriodLoop Λ ℓ)
  exact h.trans (congrArg (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) 1) hz)

theorem latticePeriodLoopHomology_evaluation [DiscreteTopology Λ]
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1) (ℓ : Λ) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 a
        (latticePeriodLoopHomology Λ ℚ ℓ) = HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod Λ a ℓ := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) 1 a
  rw [latticePeriodLoopHomology, AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation_class_class, HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class]
  change AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) (ModuleCat.of ℚ ℚ) 1 c.val
    (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (TopCat.toSSet.obj (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)) (latticePeriodLoop Λ ℓ)) = _
  rw [AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex]
  exact (HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.periodHom_eq_edge_evaluation Λ c ℓ (HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge (ℓ : V))
    (HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge_zero _) (HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge_one _)).symm

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Naturality.IntrinsicRationalPeriods OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

def nativeIntegralHomologyPeriod (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) (Betti.Scheme.schemePointSpace A.toOver)).homology 1 :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℤ) (Intrinsic.PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A) 1
    (latticePeriodLoopHomology (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℤ ℓ)

theorem nativeIntegralHomologyPeriod_rationalize (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (Betti.Scheme.schemePointSpace A.toOver) 1
        (nativeIntegralHomologyPeriod A ℓ) =
      Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) := by
  apply (Module.evalEquiv ℚ (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.rationalHomologyOne A)).injective
  ext φ
  obtain ⟨c, rfl⟩ := (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ)
    (Betti.Scheme.schemePointSpace A.toOver) 1).surjective φ
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace A.toOver) 1 c
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (Betti.Scheme.schemePointSpace A.toOver) 1
        (nativeIntegralHomologyPeriod A ℓ)) =
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace A.toOver) 1 c
      (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ))
  let X := Betti.Scheme.schemePointSpace A.toOver
  let B := HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
  let f : B ⟶ X := Intrinsic.PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A
  let zI : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains B).homology 1 :=
    latticePeriodLoopHomology (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℤ ℓ
  let zQ : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) B).homology 1 :=
    latticePeriodLoopHomology (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℚ ℓ
  have hn : AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X 1
      (nativeIntegralHomologyPeriod A ℓ) =
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) B 1 zI) :=
    (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology_naturality (R := ℚ) f 1 zI).symm
  have hz : AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) B 1 zI = zQ :=
    latticePeriodLoopHomology_rationalize (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ
  have hp := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ) f 1 c zQ
  have he := latticePeriodLoopHomology_evaluation (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 1 c) ℓ
  have hm := (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing A
    (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) c).trans
      (Intrinsic.Naturality.IntrinsicRationalPeriods.nativeH1Periods_lattice A c ℓ)
  calc
    _ = AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X 1 c
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1
          (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) B 1 zI)) :=
      congrArg (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X 1 c) hn
    _ = AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X 1 c
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1 zQ) :=
      congrArg (fun z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) B).homology 1 =>
        AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X 1 c
          (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1 z)) hz
    _ = AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) B 1
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 1 c) zQ := hp.symm
    _ = HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 1 c) ℓ := he
    _ = _ := hm.symm

end

section

/-! The two oriented triangles of a pair of singular loops form an
actual integral two-cycle. Its rationalization keeps both triangles unchanged. -/

open _root_.CategoryTheory Opposite
open scoped Simplicial

open OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients OAI.AlgebraicTopology.Products.CupCohomology
open OAI.AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison

theorem simplex_face_zero_degeneracy_one (K : SSet.{0}) (s : K _⦋1⦌) :
    K.δ 0 (K.σ 1 s) = K.σ 0 (K.δ 0 s) := by
  simpa using K.δ_comp_σ_of_le_apply (show (0 : Fin 2) ≤ (0 : Fin 1).castSucc by decide) s

theorem simplex_face_two_degeneracy_zero (K : SSet.{0}) (s : K _⦋1⦌) :
    K.δ 2 (K.σ 0 s) = K.σ 0 (K.δ 1 s) := by
  simpa using K.δ_comp_σ_of_gt_apply (show (0 : Fin 1).castSucc < (1 : Fin 2) by decide) s

variable (X Y : TopCat.{0})
  (s : (TopCat.toSSet.obj X) _⦋1⦌) (t : (TopCat.toSSet.obj Y) _⦋1⦌)

def loopTriangleChain (R : Type) [CommRing R] :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (TopCat.of (X × Y))).X 2 :=
  AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) (TopCat.toSSet.obj (TopCat.of (X × Y)))
      (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((TopCat.toSSet.obj X).σ 1 s) ((TopCat.toSSet.obj Y).σ 0 t)) -
    AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) (TopCat.toSSet.obj (TopCat.of (X × Y)))
      (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((TopCat.toSSet.obj X).σ 0 s) ((TopCat.toSSet.obj Y).σ 1 t))

theorem loopTriangleChain_closed (R : Type) [CommRing R]
    (hs : (TopCat.toSSet.obj X).δ 0 s = (TopCat.toSSet.obj X).δ 1 s)
    (ht : (TopCat.toSSet.obj Y).δ 0 t = (TopCat.toSSet.obj Y).δ 1 t) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (TopCat.of (X × Y))).d 2 1
      (loopTriangleChain X Y s t R) = 0 := by
  let KX := TopCat.toSSet.obj X
  let KY := TopCat.toSSet.obj Y
  let K := TopCat.toSSet.obj (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj (X, Y))
  let a : K _⦋2⦌ := AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) (KX.σ 1 s) (KY.σ 0 t)
  let b : K _⦋2⦌ := AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) (KX.σ 0 s) (KY.σ 1 t)
  let C := AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := R) K
  let d : C.X 2 →ₗ[R] C.X 1 := (C.d 2 1).hom
  have boundary (u : K _⦋2⦌) :
      d (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K u) =
        AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 0 u) - AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 1 u) +
          AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 2 u) := by
    let f : Fin 3 → C.X 1 :=
      fun i => ((-1 : ℤ) ^ i.val) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ i u)
    have h0 : f 0 = AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 0 u) := by
      change (1 : ℤ) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 0 u) = _
      exact one_zsmul _
    have h1 : f 1 = -AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 1 u) := by
      change (-1 : ℤ) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 1 u) = _
      exact neg_one_zsmul _
    have h2 : f 2 = AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 2 u) := by
      change (1 : ℤ) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 2 u) = _
      exact one_zsmul _
    have he : f 0 + f 1 + f 2 =
        AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 0 u) - AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 1 u) +
          AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 2 u) := by
      rw [h0, h1, h2, sub_eq_add_neg]
    exact (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain_boundary (R := R) K (n := 1) u).trans
      ((Fin.sum_univ_three f).trans he)
  have ha0 : K.δ 0 a = AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) (KX.σ 0 (KX.δ 0 s)) t :=
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex_face 1 (X, Y) (KX.σ 1 s) (KY.σ 0 t) 0).trans
      (congrArg₂ (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y)) (simplex_face_zero_degeneracy_one KX s)
        (SSet.δ_comp_σ_self_apply (S := KY) (0 : Fin 2) t))
  have ha1 : K.δ 1 a = AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) s t :=
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex_face 1 (X, Y) (KX.σ 1 s) (KY.σ 0 t) 1).trans
      (congrArg₂ (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y))
        (SSet.δ_comp_σ_self_apply (S := KX) (1 : Fin 2) s)
        (SSet.δ_comp_σ_succ_apply (S := KY) (0 : Fin 2) t))
  have ha2 : K.δ 2 a = AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) s (KY.σ 0 (KY.δ 1 t)) :=
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex_face 1 (X, Y) (KX.σ 1 s) (KY.σ 0 t) 2).trans
      (congrArg₂ (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y))
        (SSet.δ_comp_σ_succ_apply (S := KX) (1 : Fin 2) s)
        (simplex_face_two_degeneracy_zero KY t))
  have hb0 : K.δ 0 b = AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) s (KY.σ 0 (KY.δ 0 t)) :=
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex_face 1 (X, Y) (KX.σ 0 s) (KY.σ 1 t) 0).trans
      (congrArg₂ (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y))
        (SSet.δ_comp_σ_self_apply (S := KX) (0 : Fin 2) s)
        (simplex_face_zero_degeneracy_one KY t))
  have hb1 : K.δ 1 b = AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) s t :=
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex_face 1 (X, Y) (KX.σ 0 s) (KY.σ 1 t) 1).trans
      (congrArg₂ (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y))
        (SSet.δ_comp_σ_succ_apply (S := KX) (0 : Fin 2) s)
        (SSet.δ_comp_σ_self_apply (S := KY) (1 : Fin 2) t))
  have hb2 : K.δ 2 b = AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) (KX.σ 0 (KX.δ 1 s)) t :=
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex_face 1 (X, Y) (KX.σ 0 s) (KY.σ 1 t) 2).trans
      (congrArg₂ (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y)) (simplex_face_two_degeneracy_zero KX s)
        (SSet.δ_comp_σ_succ_apply (S := KY) (1 : Fin 2) t))
  have h02 : K.δ 0 a = K.δ 2 b := ha0.trans
    ((congrArg (fun v => AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) (KX.σ 0 v) t) hs).trans hb2.symm)
  have h11 : K.δ 1 a = K.δ 1 b := ha1.trans hb1.symm
  have h20 : K.δ 2 a = K.δ 0 b := ha2.trans
    ((congrArg (fun v => AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) s (KY.σ 0 v)) ht.symm).trans hb0.symm)
  change d (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K a - AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K b) = 0
  calc
    _ = d (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K a) - d (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K b) := map_sub d _ _
    _ = (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 0 a) - AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 1 a) +
          AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 2 a)) -
        (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 0 b) - AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 1 b) +
          AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K (K.δ 2 b)) :=
      congrArg₂ (fun x y : C.X 1 => x - y) (boundary a) (boundary b)
    _ = 0 := by
      rw [h02, h11, h20]
      abel

def loopTriangleCycle (R : Type) [CommRing R]
    (hs : (TopCat.toSSet.obj X).δ 0 s = (TopCat.toSSet.obj X).δ 1 s)
    (ht : (TopCat.toSSet.obj Y).δ 0 t = (TopCat.toSSet.obj Y).δ 1 t) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (TopCat.of (X × Y))) 2 :=
  ⟨loopTriangleChain X Y s t R,
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (TopCat.of (X × Y))) 1 _).mpr
      (loopTriangleChain_closed X Y s t R hs ht)⟩

theorem loopTriangleChain_rationalize :
    AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℚ) (TopCat.of (X × Y)) 2 (loopTriangleChain X Y s t ℤ) =
      loopTriangleChain X Y s t ℚ := by
  let Z := AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj (X, Y)
  let K := TopCat.toSSet.obj Z
  let a : K _⦋2⦌ := AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((TopCat.toSSet.obj X).σ 1 s)
    ((TopCat.toSSet.obj Y).σ 0 t)
  let b : K _⦋2⦌ := AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((TopCat.toSSet.obj X).σ 0 s)
    ((TopCat.toSSet.obj Y).σ 1 t)
  let aI : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains Z).X 2 := AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) K a
  let bI : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains Z).X 2 := AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) K b
  let f := AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial (R := ℚ) K 2
  have ha : f aI = AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) K a := AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial_simplex K 2 a
  have hb : f bI = AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) K b := AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial_simplex K 2 b
  exact (map_sub f aI bI).trans
    (congrArg₂ (fun x y : (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℚ) K).X 2 => x - y) ha hb)

theorem loopTriangleCycle_rationalize
    (hs : (TopCat.toSSet.obj X).δ 0 s = (TopCat.toSSet.obj X).δ 1 s)
    (ht : (TopCat.toSSet.obj Y).δ 0 t = (TopCat.toSSet.obj Y).δ 1 t) :
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) (TopCat.of (X × Y)) 2
        (loopTriangleCycle X Y s t ℤ hs ht) = loopTriangleCycle X Y s t ℚ hs ht := by
  apply Subtype.ext
  exact loopTriangleChain_rationalize X Y s t

theorem oneCocycle_degenerate_evaluation {R : Type} [CommRing R]
    (K : SSet.{0}) (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) 1)
    (v : K _⦋0⦌) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) (K.σ 0 v) c.val = 0 := by
  have h := congrArg (fun a => AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R)
      (K.σ 0 (K.σ 0 v)) a)
    (AlgebraicTopology.Cohomology.Singular.Evaluation.cochainCocycle_d_eq_zero (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) 1 2 c)
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_coboundary_apply] at h
  have h0 : K.δ 0 (K.σ 0 (K.σ 0 v)) = K.σ 0 v :=
    SSet.δ_comp_σ_self_apply (S := K) (0 : Fin 2) (K.σ 0 v)
  have h1 : K.δ 1 (K.σ 0 (K.σ 0 v)) = K.σ 0 v :=
    SSet.δ_comp_σ_succ_apply (S := K) (0 : Fin 2) (K.σ 0 v)
  have h2 : K.δ 2 (K.σ 0 (K.σ 0 v)) = K.σ 0 v :=
    (simplex_face_two_degeneracy_zero K (K.σ 0 v)).trans
      (congrArg (fun w => K.σ 0 w) (SSet.δ_comp_σ_succ_apply (S := K) (0 : Fin 1) v))
  simpa [Fin.sum_univ_three, h0, h1, h2] using h

end

/-! The two literal loop triangles evaluate the degree-one cup product
as the determinant of its horizontal and vertical edge values. -/

open _root_.CategoryTheory Opposite
open scoped Simplicial

open OAI.AlgebraicTopology.Products.CupCohomology OAI.AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison

theorem frontFace_one_one (K : SSet.{0}) (s : K _⦋2⦌) :
    AlgebraicTopology.Products.SimplexFaceIdentities.frontFace K 1 1 s = K.δ 2 s := by
  have h : AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion 1 1 = SimplexCategory.δ (2 : Fin 3) := by
    ext i
    fin_cases i <;> rfl
  change K.map (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion 1 1).op s = K.map (SimplexCategory.δ (2 : Fin 3)).op s
  exact congrArg (fun f => K.map f.op s) h

theorem backFace_one_one (K : SSet.{0}) (s : K _⦋2⦌) :
    AlgebraicTopology.Products.SimplexFaceIdentities.backFace K 1 1 s = K.δ 0 s := by
  have h : AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion 1 1 = SimplexCategory.δ (0 : Fin 3) := by
    ext i
    fin_cases i <;> rfl
  change K.map (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion 1 1).op s = K.map (SimplexCategory.δ (0 : Fin 3)).op s
  exact congrArg (fun f => K.map f.op s) h

theorem simplicialTrianglePair_cup {R : Type} [CommRing R] (K : SSet.{0})
    (u v : K _⦋2⦌) (H V : K _⦋1⦌)
    (hu2 : K.δ 2 u = H) (hu0 : K.δ 0 u = V)
    (hv2 : K.δ 2 v = V) (hv0 : K.δ 0 v = H)
    (a b : (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)).X 1) :
    AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K (ModuleCat.of R R) 2 (AlgebraicTopology.Products.Cup.cup K a b)
        (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K u - AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K v) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) H a *
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) V b -
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) V a *
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) H b := by
  let A (w : K _⦋1⦌) := AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) w a
  let B (w : K _⦋1⦌) := AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of R R) w b
  let f := AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K (ModuleCat.of R R) 2 (AlgebraicTopology.Products.Cup.cup K a b)
  have heval (w : K _⦋2⦌) : f (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K w) =
      A (K.δ 2 w) * B (K.δ 0 w) :=
    (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex K (ModuleCat.of R R) (AlgebraicTopology.Products.Cup.cup K a b) w).trans
      ((AlgebraicTopology.Products.Cup.evaluation_cup K a b w).trans
        (congrArg₂ (fun x y : R => x * y)
          (congrArg A (frontFace_one_one K w)) (congrArg B (backFace_one_one K w))))
  change f (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K u - AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K v) =
    A H * B V - A V * B H
  calc
    _ = f (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K u) - f (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := R) K v) := map_sub f _ _
    _ = A (K.δ 2 u) * B (K.δ 0 u) - A (K.δ 2 v) * B (K.δ 0 v) :=
      congrArg₂ (fun x y : R => x - y) (heval u) (heval v)
    _ = _ := by rw [hu2, hu0, hv2, hv0]

variable (X Y : TopCat.{0})
  (s : (TopCat.toSSet.obj X) _⦋1⦌) (t : (TopCat.toSSet.obj Y) _⦋1⦌)

def loopHorizontalEdge : (TopCat.toSSet.obj (TopCat.of (X × Y))) _⦋1⦌ :=
  AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) s ((TopCat.toSSet.obj Y).σ 0 ((TopCat.toSSet.obj Y).δ 1 t))

def loopVerticalEdge : (TopCat.toSSet.obj (TopCat.of (X × Y))) _⦋1⦌ :=
  AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) ((TopCat.toSSet.obj X).σ 0 ((TopCat.toSSet.obj X).δ 1 s)) t

local notation "KX" => TopCat.toSSet.obj X
local notation "KY" => TopCat.toSSet.obj Y
local notation "KP" => TopCat.toSSet.obj
  (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.obj (X, Y))

theorem loopTriangle_first_frontFace :
    (KP).δ 2 (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((KX).σ 1 s) ((KY).σ 0 t)) =
      AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) s ((KY).σ 0 ((KY).δ 1 t)) :=
  (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex_face 1 (X, Y) ((KX).σ 1 s) ((KY).σ 0 t) 2).trans
    (congrArg₂ (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y))
      (SSet.δ_comp_σ_succ_apply (S := KX) (1 : Fin 2) s)
      (simplex_face_two_degeneracy_zero KY t))

theorem loopTriangle_first_backFace (hs : (KX).δ 0 s = (KX).δ 1 s) :
    (KP).δ 0 (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((KX).σ 1 s) ((KY).σ 0 t)) =
      AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) ((KX).σ 0 ((KX).δ 1 s)) t :=
  (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex_face 1 (X, Y) ((KX).σ 1 s) ((KY).σ 0 t) 0).trans
    ((congrArg₂ (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y)) (simplex_face_zero_degeneracy_one KX s)
      (SSet.δ_comp_σ_self_apply (S := KY) (0 : Fin 2) t)).trans
      (congrArg (fun w => AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) ((KX).σ 0 w) t) hs))

theorem loopTriangle_second_frontFace :
    (KP).δ 2 (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((KX).σ 0 s) ((KY).σ 1 t)) =
      AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) ((KX).σ 0 ((KX).δ 1 s)) t :=
  (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex_face 1 (X, Y) ((KX).σ 0 s) ((KY).σ 1 t) 2).trans
    (congrArg₂ (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y)) (simplex_face_two_degeneracy_zero KX s)
      (SSet.δ_comp_σ_succ_apply (S := KY) (1 : Fin 2) t))

theorem loopTriangle_second_backFace (ht : (KY).δ 0 t = (KY).δ 1 t) :
    (KP).δ 0 (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((KX).σ 0 s) ((KY).σ 1 t)) =
      AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) s ((KY).σ 0 ((KY).δ 1 t)) :=
  (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex_face 1 (X, Y) ((KX).σ 0 s) ((KY).σ 1 t) 0).trans
    ((congrArg₂ (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y))
      (SSet.δ_comp_σ_self_apply (S := KX) (0 : Fin 2) s)
      (simplex_face_zero_degeneracy_one KY t)).trans
      (congrArg (fun w => AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) s ((KY).σ 0 w)) ht))

theorem loopTriangleChain_cup {R : Type} [CommRing R]
    (hs : (TopCat.toSSet.obj X).δ 0 s = (TopCat.toSSet.obj X).δ 1 s)
    (ht : (TopCat.toSSet.obj Y).δ 0 t = (TopCat.toSSet.obj Y).δ 1 t)
    (a b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) (TopCat.of (X × Y))).X 1) :
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of R R) (TopCat.of (X × Y)) 2
        (AlgebraicTopology.Products.Cup.singularCup (TopCat.of (X × Y)) a b) (loopTriangleChain X Y s t R) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of (X × Y))) (ModuleCat.of R R)
          (loopHorizontalEdge X Y s t) a *
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of (X × Y))) (ModuleCat.of R R)
          (loopVerticalEdge X Y s t) b -
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of (X × Y))) (ModuleCat.of R R)
          (loopVerticalEdge X Y s t) a *
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of (X × Y))) (ModuleCat.of R R)
          (loopHorizontalEdge X Y s t) b := by
  exact simplicialTrianglePair_cup (R := R) KP
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((KX).σ 1 s) ((KY).σ 0 t))
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((KX).σ 0 s) ((KY).σ 1 t))
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) s ((KY).σ 0 ((KY).δ 1 t)))
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 1 (X, Y) ((KX).σ 0 ((KX).δ 1 s)) t)
    (loopTriangle_first_frontFace X Y s t) (loopTriangle_first_backFace X Y s t hs)
    (loopTriangle_second_frontFace X Y s t) (loopTriangle_second_backFace X Y s t ht) a b

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.Loop
