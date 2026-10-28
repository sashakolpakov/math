import OAI.AlgebraicGeometry.HodgeConjecture.GeometricFour
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ComplexOperations
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupAppend
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupPermutation
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CanonicalExterior
import OAI.AlgebraicGeometry.ComplexMultiplication.RealizedHodgeMaps
import OAI.AlgebraicTopology.Kunneth.CupPullbackSingular

/-! # Geometric Operations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.GeometricOperations.LefschetzNormalization.Geometry

noncomputable section

/-! Construct the product and Hodge-map transfer laws for the concrete
cycle-image predicates of LefschetzNormalization. The explicit intermediate inputs are the
native cycle pullback/exterior-product theorems, exterior cohomology, and
weight-one algebraicity. None of these inputs asserts a switch is algebraic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct Classical

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

theorem pulledClass_pullback {v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : X.toOver ⟶ Y.toOver)
    (π : Y.toOver ⟶ R.abelianVariety.toOver) (a : LefschetzNormalization.G E) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (GeometricCoefficients.LefschetzNormalization.Geometry.pulledClass E R Y π a) =
      GeometricCoefficients.LefschetzNormalization.Geometry.pulledClass E R X (f ≫ π) a :=
  CMReduction.CupPullback.CM.Construction.scheme_pullback_comp (R := ℂ) f π 1 (R.complexComparison (LefschetzNormalization.embeddingGenerator E a))

theorem pairClass_pullback {u v : LefschetzNormalization.Sign E}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u))
    (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : X.toOver ⟶ Y.toOver)
    (πR : Y.toOver ⟶ R.abelianVariety.toOver)
    (πT : Y.toOver ⟶ T.abelianVariety.toOver) (a b : LefschetzNormalization.G E) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 2 f (GeometricCoefficients.LefschetzNormalization.Geometry.pairClass E R T Y πR πT a b) =
      GeometricCoefficients.LefschetzNormalization.Geometry.pairClass E R T X (f ≫ πR) (f ≫ πT) a b := by
  exact (AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) 1 1
    (GeometricCoefficients.LefschetzNormalization.Geometry.pulledClass E R Y πR a) (GeometricCoefficients.LefschetzNormalization.Geometry.pulledClass E T Y πT b)).trans
      (congrArg₂ (fun x y : X.complexCohomology 1 =>
          AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 1 1 x y)
        (pulledClass_pullback E R f πR a) (pulledClass_pullback E T f πT b))

theorem A₂_pullback (R : GeometricFour.LefschetzNormalization.Geometry.RealizationFamily E) (hLineBundleCycles : CMReduction.CycleOperations.CM.Construction.LineBundleCyclesInput)
    (u v : LefschetzNormalization.Sign E) (a b : LefschetzNormalization.G E) (h : GeometricFour.LefschetzNormalization.Geometry.A₂ E R u v a b)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πu : X.toOver ⟶ (R u).abelianVariety.toOver)
    (πv : X.toOver ⟶ (R v).abelianVariety.toOver) :
    GeometricCoefficients.LefschetzNormalization.Geometry.pairClass E (R u) (R v) X πu πv a b ∈ X.complexGeometricAlgebraicClasses 1 := by
  let Y := Albanese.Construction.SegreClosed.abelianProduct (R u).abelianVariety (R v).abelianVariety
  let f : X.toOver ⟶ Y.toOver := CartesianMonoidalCategory.lift πu πv
  have ht := CMReduction.ComplexOperations.CM.Construction.complex_pullback_algebraic hLineBundleCycles f 1 _ h
  change Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 2 f
    (GeometricCoefficients.LefschetzNormalization.Geometry.pairClass E (R u) (R v) Y.variety (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _) a b) ∈ _ at ht
  have he := pairClass_pullback E (R u) (R v) f
    (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _) a b
  have hfu : f ≫ CartesianMonoidalCategory.fst _ _ = πu :=
    CartesianMonoidalCategory.lift_fst πu πv
  have hfv : f ≫ CartesianMonoidalCategory.snd _ _ = πv :=
    CartesianMonoidalCategory.lift_snd πu πv
  rw [hfu, hfv] at he
  exact he ▸ ht

theorem fourClass_eq_h1Cup {v : LefschetzNormalization.FourTypes E}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) (a : Fin 4 → LefschetzNormalization.G E) :
    GeometricFour.LefschetzNormalization.Geometry.fourClass E R X π a = CMReduction.IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace X.toOver) 4
      (fun i => GeometricCoefficients.LefschetzNormalization.Geometry.pulledClass E (R i) X (π i) (a i)) := by
  exact (CMReduction.CupAppend.CM.Construction.h1Cup_four (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver)
    (fun i => GeometricCoefficients.LefschetzNormalization.Geometry.pulledClass E (R i) X (π i) (a i))).symm

theorem fourClass_pullback {v : LefschetzNormalization.FourTypes E}
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : X.toOver ⟶ Y.toOver)
    (π : ∀ i, Y.toOver ⟶ (R i).abelianVariety.toOver) (a : Fin 4 → LefschetzNormalization.G E) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 4 f (GeometricFour.LefschetzNormalization.Geometry.fourClass E R Y π a) =
      GeometricFour.LefschetzNormalization.Geometry.fourClass E R X (fun i => f ≫ π i) a := by
  exact (AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) 2 2
    (GeometricCoefficients.LefschetzNormalization.Geometry.pairClass E (R 0) (R 1) Y (π 0) (π 1) (a 0) (a 1))
    (GeometricCoefficients.LefschetzNormalization.Geometry.pairClass E (R 2) (R 3) Y (π 2) (π 3) (a 2) (a 3))).trans
      (congrArg₂ (fun x y : X.complexCohomology 2 =>
          AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 2 2 x y)
        (pairClass_pullback E (R 0) (R 1) f (π 0) (π 1) (a 0) (a 1))
        (pairClass_pullback E (R 2) (R 3) f (π 2) (π 3) (a 2) (a 3)))

theorem A₄_pullback (R : GeometricFour.LefschetzNormalization.Geometry.RealizationFamily E) (hLineBundleCycles : CMReduction.CycleOperations.CM.Construction.LineBundleCyclesInput)
    (v : LefschetzNormalization.FourTypes E) (a : Fin 4 → LefschetzNormalization.G E) (h : GeometricFour.LefschetzNormalization.Geometry.A₄ E R v a)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R (v i)).abelianVariety.toOver) :
    GeometricFour.LefschetzNormalization.Geometry.fourClass E (fun i => R (v i)) X π a ∈ X.complexGeometricAlgebraicClasses 2 := by
  let B : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := fun i => (R (v i)).abelianVariety
  let f : X.toOver ⟶ (CMVariety.Products.CM.Abelian.fourProduct B).toOver :=
    Fan.IsLimit.lift (CMVariety.Products.CM.Abelian.fourProductIsLimit B) π
  have ht := CMReduction.ComplexOperations.CM.Construction.complex_pullback_algebraic hLineBundleCycles f 2 _ h
  erw [fourClass_pullback E (fun i => R (v i)) f] at ht
  have he (i : Fin 4) : f ≫ CMVariety.Products.CM.Abelian.fourProjection B i = π i :=
    Fan.IsLimit.fac (CMVariety.Products.CM.Abelian.fourProductIsLimit B) π i
  have hπ : (fun i => f ≫ CMVariety.Products.CM.Abelian.fourProjection B i) = π := funext he
  change GeometricFour.LefschetzNormalization.Geometry.fourClass E (fun i => R (v i)) X
    (fun i => f ≫ CMVariety.Products.CM.Abelian.fourProjection B i) a ∈ _ at ht
  rw [hπ] at ht
  exact ht

/-- Products of two actual divisor classes, in any prescribed slot order,
give the original four-factor class. The permutation changes only its sign. -/
theorem A₄_of_pairs (R : GeometricFour.LefschetzNormalization.Geometry.RealizationFamily E)
    (hLineBundleCycles : CMReduction.CycleOperations.CM.Construction.LineBundleCyclesInput) (hThomClass : CMReduction.CycleOperations.CM.Construction.ExteriorInput)
    (hExteriorCohomology : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology)
    (v : LefschetzNormalization.FourTypes E) (a : Fin 4 → LefschetzNormalization.G E) (p : Equiv.Perm (Fin 4))
    (h01 : GeometricFour.LefschetzNormalization.Geometry.A₂ E R (v (p 0)) (v (p 1)) (a (p 0)) (a (p 1)))
    (h23 : GeometricFour.LefschetzNormalization.Geometry.A₂ E R (v (p 2)) (v (p 3)) (a (p 2)) (a (p 3))) :
    GeometricFour.LefschetzNormalization.Geometry.A₄ E R v a := by
  let B : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := fun i => (R (v i)).abelianVariety
  let X := CMVariety.Products.CM.Abelian.fourProduct B
  let π := CMVariety.Products.CM.Abelian.fourProjection B
  let x (i : Fin 4) := GeometricCoefficients.LefschetzNormalization.Geometry.pulledClass E (R (v i)) X.variety (π i) (a i)
  have hleft := A₂_pullback E R hLineBundleCycles _ _ _ _ h01 X.variety (π (p 0)) (π (p 1))
  have hright := A₂_pullback E R hLineBundleCycles _ _ _ _ h23 X.variety (π (p 2)) (π (p 3))
  have hp : CMReduction.IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace X.toOver) 4 (fun i => x (p i)) ∈
      X.variety.complexGeometricAlgebraicClasses 2 := by
    rw [CMReduction.CupAppend.CM.Construction.h1Cup_four]
    exact CMReduction.ComplexOperations.CM.Construction.complex_cup_algebraic hLineBundleCycles hThomClass X.variety 1 1 _ _ hleft hright
  have ht := CMReduction.CupPermutation.CM.Construction.h1Cup_perm_mem (CMReduction.CanonicalExterior.CM.Construction.canonicalExterior hExteriorCohomology X) 2 (fun i => x (p i)) p.symm hp
  have hs : (fun i : Fin 4 => x (p i)) ∘ p.symm = x :=
    funext (fun i => congrArg x (p.apply_symm_apply i))
  rw [hs] at ht
  change GeometricFour.LefschetzNormalization.Geometry.fourClass E (fun i => R (v i)) X.variety π a ∈ _
  rw [fourClass_eq_h1Cup]
  exact ht

/-- Applying fullness to the marked rational Hodge map yields the exact
coefficient of an actual algebraic pullback on every complex vector. -/
theorem hodgeMap_complexComparison (hDegreeTwo : ComplexMultiplication.KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic)
    {u v : LefschetzNormalization.Sign E} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u))
    (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v)) (f : E →ₗ[ℚ] E)
    (hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E u) (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) f) :
    ∃ (r : ℚ) (g : T.abelianVariety.toOver ⟶ R.abelianVariety.toOver),
      IsMonHom g ∧ ∀ x : ComplexMultiplication.WeightOne.CM.Complexification E,
        T.complexComparison (f.baseChange ℂ x) = (r : ℂ) •
          Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g (R.complexComparison x) := by
  obtain ⟨r, g, hg, he⟩ := R.realizedMap_eq_rational_pullback hDegreeTwo T f hf
  refine ⟨r, g, hg, ?_⟩
  intro x
  have hm : T.comparison.toLinearMap.comp f =
      (R.realizedMap T f).comp R.comparison.toLinearMap := by
    ext y
    simp only [ComplexMultiplication.CMKnownResults.CM.HodgeRealization.realizedMap, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hc := congrArg (fun q : E →ₗ[ℚ] T.abelianVariety.variety.rationalCohomology 1 =>
    q.baseChange ℂ x) hm
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hc
  change T.abelianVariety.h1ScalarExtension
    (T.comparison.toLinearMap.baseChange ℂ (f.baseChange ℂ x)) = _
  rw [hc, he, LinearMap.baseChange_smul, LinearMap.smul_apply]
  refine (map_ratCast_smul T.abelianVariety.h1ScalarExtension ℚ ℂ r _).trans ?_
  have hp := Pairs.CM.SurfaceConstruction.complexification_pullback g 1
    (R.comparison.toLinearMap.baseChange ℂ x)
  exact congrArg (fun z => (r : ℂ) • z) hp

/-- The tensor product of four marked rational Hodge maps is a scalar
multiple of the pullback along the constructed product morphism. -/
theorem A₄_hodge_transfer (R : GeometricFour.LefschetzNormalization.Geometry.RealizationFamily E)
    (hLineBundleCycles : CMReduction.CycleOperations.CM.Construction.LineBundleCyclesInput) (hDegreeTwo : ComplexMultiplication.KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic)
    (u v : LefschetzNormalization.FourTypes E) (a b : Fin 4 → LefschetzNormalization.G E) (f : Fin 4 → (E →ₗ[ℚ] E))
    (hf : ∀ i, ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (u i)) (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)) (f i))
    (he : ∀ i, (f i).baseChange ℂ (LefschetzNormalization.embeddingGenerator E (a i)) = LefschetzNormalization.embeddingGenerator E (b i))
    (h : GeometricFour.LefschetzNormalization.Geometry.A₄ E R u a) : GeometricFour.LefschetzNormalization.Geometry.A₄ E R v b := by
  choose r g _hg hcomp using fun i =>
    hodgeMap_complexComparison E hDegreeTwo (R (u i)) (R (v i)) (f i) (hf i)
  let B : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := fun i => (R (v i)).abelianVariety
  let X := CMVariety.Products.CM.Abelian.fourProduct B
  let π := CMVariety.Products.CM.Abelian.fourProjection B
  have ht := A₄_pullback E R hLineBundleCycles u a h X.variety (fun i => π i ≫ g i)
  rw [fourClass_eq_h1Cup] at ht
  change GeometricFour.LefschetzNormalization.Geometry.fourClass E (fun i => R (v i)) X.variety π b ∈ _
  rw [fourClass_eq_h1Cup]
  have hv (i : Fin 4) : GeometricCoefficients.LefschetzNormalization.Geometry.pulledClass E (R (v i)) X.variety (π i) (b i) =
      (r i : ℂ) • GeometricCoefficients.LefschetzNormalization.Geometry.pulledClass E (R (u i)) X.variety (π i ≫ g i) (a i) := by
    have hi := hcomp i (LefschetzNormalization.embeddingGenerator E (a i))
    rw [he i] at hi
    unfold GeometricCoefficients.LefschetzNormalization.Geometry.pulledClass
    rw [hi, map_smul, CMReduction.CupPullback.CM.Construction.scheme_pullback_comp]
  simp only [hv]
  rw [MultilinearMap.map_smul_univ]
  exact (X.variety.complexGeometricAlgebraicClasses 2).smul_mem _ ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.GeometricOperations.LefschetzNormalization.Geometry
