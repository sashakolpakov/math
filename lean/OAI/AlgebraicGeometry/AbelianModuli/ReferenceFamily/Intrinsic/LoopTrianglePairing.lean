import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralLoopTriangles
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyPairingAntisymmetry

/-! # Loop Triangle Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LoopTrianglePairing

noncomputable section

/-! Evaluation on the literal integral period triangles equals the
original homology pairing. Degree-one cup generation proves the equality
for every original degree-two class. -/

open _root_.CategoryTheory Opposite
open scoped Simplicial

open OAI.AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

private theorem mapped_simplicialTrianglePair_cup
    {K L : SSet.{0}} (f : K ⟶ L)
    (u v : K _⦋2⦌) (H V : K _⦋1⦌)
    (hu2 : K.δ 2 u = H) (hu0 : K.δ 0 u = V)
    (hv2 : K.δ 2 v = V) (hv0 : K.δ 0 v = H)
    (a b : (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains L (ModuleCat.of ℚ ℚ)).X 1) :
    AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv L (ModuleCat.of ℚ ℚ) 2 (AlgebraicTopology.Products.Cup.cup L a b)
      ((AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) f).f 2
        (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) K u - AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) K v)) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation L (ModuleCat.of ℚ ℚ) (f.app (op ⦋1⦌) H) a *
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation L (ModuleCat.of ℚ ℚ) (f.app (op ⦋1⦌) V) b -
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation L (ModuleCat.of ℚ ℚ) (f.app (op ⦋1⦌) V) a *
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation L (ModuleCat.of ℚ ℚ) (f.app (op ⦋1⦌) H) b := by
  rw [map_sub, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex]
  exact Integral.Loop.simplicialTrianglePair_cup L (f.app (op ⦋2⦌) u) (f.app (op ⦋2⦌) v)
    (f.app (op ⦋1⦌) H) (f.app (op ⦋1⦌) V)
    ((SSet.δ_naturality_apply f 2 u).symm.trans (congrArg (f.app (op ⦋1⦌)) hu2))
    ((SSet.δ_naturality_apply f 0 u).symm.trans (congrArg (f.app (op ⦋1⦌)) hu0))
    ((SSet.δ_naturality_apply f 2 v).symm.trans (congrArg (f.app (op ⦋1⦌)) hv2))
    ((SSet.δ_naturality_apply f 0 v).symm.trans (congrArg (f.app (op ⦋1⦌)) hv0)) a b

private theorem mapped_loopTriangleChain_cup (X Y Z : TopCat.{0})
    (s : (TopCat.toSSet.obj X) _⦋1⦌) (t : (TopCat.toSSet.obj Y) _⦋1⦌)
    (hs : (TopCat.toSSet.obj X).δ 0 s = (TopCat.toSSet.obj X).δ 1 s)
    (ht : (TopCat.toSSet.obj Y).δ 0 t = (TopCat.toSSet.obj Y).δ 1 t)
    (f : TopCat.of (X × Y) ⟶ Z)
    (a b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) Z).X 1) :
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) Z 2 (AlgebraicTopology.Products.Cup.singularCup Z a b)
        ((AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) f).f 2 (Integral.Loop.loopTriangleChain X Y s t ℚ)) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Z) (ModuleCat.of ℚ ℚ)
          ((TopCat.toSSet.map f).app (op ⦋1⦌) (Integral.Loop.loopHorizontalEdge X Y s t)) a *
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Z) (ModuleCat.of ℚ ℚ)
          ((TopCat.toSSet.map f).app (op ⦋1⦌) (Integral.Loop.loopVerticalEdge X Y s t)) b -
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Z) (ModuleCat.of ℚ ℚ)
          ((TopCat.toSSet.map f).app (op ⦋1⦌) (Integral.Loop.loopVerticalEdge X Y s t)) a *
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Z) (ModuleCat.of ℚ ℚ)
          ((TopCat.toSSet.map f).app (op ⦋1⦌) (Integral.Loop.loopHorizontalEdge X Y s t)) b := by
  exact mapped_simplicialTrianglePair_cup (TopCat.toSSet.map f)
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((TopCat.toSSet.obj X).σ 1 s) ((TopCat.toSSet.obj Y).σ 0 t))
    (AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.pairSimplex 2 (X, Y) ((TopCat.toSSet.obj X).σ 0 s) ((TopCat.toSSet.obj Y).σ 1 t))
    (Integral.Loop.loopHorizontalEdge X Y s t) (Integral.Loop.loopVerticalEdge X Y s t)
    (Integral.Loop.loopTriangle_first_frontFace X Y s t) (Integral.Loop.loopTriangle_first_backFace X Y s t hs)
    (Integral.Loop.loopTriangle_second_frontFace X Y s t) (Integral.Loop.loopTriangle_second_backFace X Y s t ht) a b

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (ℓ μ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)

theorem nativeLoopTriangleCycle_cup_evaluation
    (a b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)).X 1) :
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 2
        (AlgebraicTopology.Products.Cup.singularCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) a b) (IntegralLoopTriangles.nativeLoopTriangleCycle A ℓ μ ℚ).val =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) (ModuleCat.of ℚ ℚ)
          (PeriodLoopClasses.nativePeriodLoop A ℓ) a *
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) (ModuleCat.of ℚ ℚ)
          (PeriodLoopClasses.nativePeriodLoop A μ) b -
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) (ModuleCat.of ℚ ℚ)
          (PeriodLoopClasses.nativePeriodLoop A μ) a *
        AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) (ModuleCat.of ℚ ℚ)
          (PeriodLoopClasses.nativePeriodLoop A ℓ) b := by
  have h := mapped_loopTriangleChain_cup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)
    (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (PeriodLoopClasses.nativePeriodLoop A ℓ) (PeriodLoopClasses.nativePeriodLoop A μ)
    (PeriodLoopClasses.nativePeriodLoop_closed A ℓ) (PeriodLoopClasses.nativePeriodLoop_closed A μ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) a b
  rw [IntegralLoopTriangles.nativeLoopHorizontalEdge_multiplication, IntegralLoopTriangles.nativeLoopVerticalEdge_multiplication] at h
  exact h

def nativeLoopTriangleEvaluation : A.variety.rationalCohomology 2 →ₗ[ℚ] ℚ where
  toFun c := AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 2 c
    (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 2
      (IntegralLoopTriangles.nativeIntegralLoopTriangleClass A ℓ μ))
  map_add' c d := by simp only [map_add, LinearMap.add_apply]
  map_smul' r c := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]

theorem nativeLoopTriangleEvaluation_cup (a b : A.variety.rationalCohomology 1) :
    nativeLoopTriangleEvaluation A ℓ μ (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1 a b) =
      HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A a (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) *
        HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A b (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) μ) -
      HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A a (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) μ) *
        HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A b (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) := by
  obtain ⟨a, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 a
  obtain ⟨b, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 b
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 2
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 a)
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 b))
    (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 2
      (IntegralLoopTriangles.nativeIntegralLoopTriangleClass A ℓ μ)) = _
  rw [IntegralLoopTriangles.nativeIntegralLoopTriangleClass_rationalize A ℓ μ,
    AlgebraicTopology.Products.CupCohomology.cohomologyCupWith_class_class, AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation_class_class]
  change AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 2
    (AlgebraicTopology.Products.Cup.singularCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) a.val b.val) (IntegralLoopTriangles.nativeLoopTriangleCycle A ℓ μ ℚ).val = _
  rw [nativeLoopTriangleCycle_cup_evaluation]
  exact congrArg₂ (fun x y : ℚ => x - y)
    (congrArg₂ (fun x y : ℚ => x * y)
      (PeriodLoopClasses.nativePeriodLoop_cocycle_evaluation A a ℓ) (PeriodLoopClasses.nativePeriodLoop_cocycle_evaluation A b μ))
    (congrArg₂ (fun x y : ℚ => x * y)
      (PeriodLoopClasses.nativePeriodLoop_cocycle_evaluation A a μ) (PeriodLoopClasses.nativePeriodLoop_cocycle_evaluation A b ℓ))

private theorem homologyCup_pairing_nativePeriods (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (v w : RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) (a b : A.variety.rationalCohomology 1) :
    HomologyCrossPairing.homologyClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1 a b)
      (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v) (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A w) =
      HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A a v * HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A b w -
        HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A a w * HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A b v := by
  have h := CupHomologyPairing.homologyClassPairing_cup A a b (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v) (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A w)
  exact h.trans (congrArg₂ (fun x y : ℚ => x - y)
    (congrArg₂ (fun x y : ℚ => x * y)
      (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing A v a) (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing A w b))
    ((congrArg₂ (fun x y : ℚ => x * y)
      (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing A v b) (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing A w a)).trans
        (mul_comm _ _)))

theorem nativeLoopTriangleEvaluation_eq_original (c : A.variety.rationalCohomology 2) :
    nativeLoopTriangleEvaluation A ℓ μ c =
      HomologyCrossPairing.homologyClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) c
        (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ))
        (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) μ)) := by
  let F : A.variety.rationalCohomology 2 →ₗ[ℚ] ℚ := {
    toFun d := nativeLoopTriangleEvaluation A ℓ μ d - HomologyPairingAntisymmetry.nativeHomologyPairingLinear A d
      (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ))
      (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) μ))
    map_add' d e := by simp only [map_add, LinearMap.add_apply]; ring
    map_smul' r d := by
      simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
      ring }
  have ht : F.ker = ⊤ := CupSpanning.abelianH2_cup_spanned A F.ker (fun a b => by
    change nativeLoopTriangleEvaluation A ℓ μ _ - HomologyPairingAntisymmetry.nativeHomologyPairingLinear A _ _ _ = 0
    apply sub_eq_zero.mpr
    have h := homologyCup_pairing_nativePeriods A
      (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ)
      (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) μ) a b
    have hp := congrArg (fun q : HomologyCrossPairing.firstHomology (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) →ₗ[ℚ]
        HomologyCrossPairing.firstHomology (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) →ₗ[ℚ] ℚ =>
      q (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ))
        (HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) μ)))
      (HomologyPairingAntisymmetry.nativeHomologyPairingLinear_apply A (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1 a b))
    exact (nativeLoopTriangleEvaluation_cup A ℓ μ a b).trans (hp.trans h).symm)
  have hc : F c = 0 := (show c ∈ F.ker from ht.symm ▸ Submodule.mem_top)
  change nativeLoopTriangleEvaluation A ℓ μ c - HomologyPairingAntisymmetry.nativeHomologyPairingLinear A c _ _ = 0 at hc
  rw [HomologyPairingAntisymmetry.nativeHomologyPairingLinear_apply] at hc
  exact sub_eq_zero.mp hc

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LoopTrianglePairing
