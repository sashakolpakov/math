import OAI.AlgebraicGeometry.ComplexMultiplication.CM.KnownRealization
import OAI.AlgebraicTopology.Kunneth.CupPullbackSingular
import OAI.AlgebraicGeometry.Cycles.Functoriality.SupportClass
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Surface Construction Q -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionQ.CM

noncomputable section

/-!
Native geometric helpers for SurfaceConstruction. These do not assert the missing ThetaCycle
existence of a surface with nonzero fundamental-class pairing. The surface
and its maps are supplied as geometric data. The Functoriality compatibility proposition
is an explicit hypothesis; no statement stub is used as a theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

/-- The actual product map of four algebraic maps. -/
def productMap {A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    {π : ∀ i, X.toOver ⟶ (A i).toOver}
    (hproduct : IsLimit (Fan.mk X.toOver π))
    (f : ∀ i, S.toOver ⟶ (A i).toOver) : S.toOver ⟶ X.toOver :=
  Fan.IsLimit.lift hproduct f

@[simp]
theorem productMap_proj {A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    {π : ∀ i, X.toOver ⟶ (A i).toOver}
    (hproduct : IsLimit (Fan.mk X.toOver π))
    (f : ∀ i, S.toOver ⟶ (A i).toOver) (i : Fin 4) :
    productMap hproduct f ≫ π i = f i :=
  Fan.IsLimit.fac hproduct f i

/-- Every algebraic map between these projective varieties is proper. -/
theorem map_isProper {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : S.toOver ⟶ X.toOver) : IsProper f.left := by
  have hw : f.left ≫ X.structureMap = S.structureMap := f.w
  have hp : IsProper (f.left ≫ X.structureMap) := by
    rw [hw]
    exact S.presentation.isProper
  exact @IsProper.of_comp _ _ _ f.left X.structureMap hp
    X.presentation.isProper.toIsSeparated

/-- The native fourfold cup class, with the same association as SurfaceConstruction. -/
def fourCup (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Fin 4 → X.complexCohomology 1) : X.complexCohomology 4 :=
  AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 2 2
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 1 1 (u 0) (u 1))
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 1 1 (u 2) (u 3))

/-- Cup naturality on actual scheme Betti cohomology. -/
theorem schemePullback_cup {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : S.toOver ⟶ X.toOver) (p q : ℕ)
    (a : X.complexCohomology p) (b : X.complexCohomology q) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) (p + q) f
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) p q a b) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace S.toOver) p q
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) p f a)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) q f b) :=
  AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) p q a b

theorem schemePullback_fourCup {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : S.toOver ⟶ X.toOver) (u : Fin 4 → X.complexCohomology 1) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 4 f (fourCup X u) =
      fourCup S (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (u i)) := by
  unfold fourCup
  rw [schemePullback_cup f 2 2, schemePullback_cup f 1 1,
    schemePullback_cup f 1 1]

theorem schemePullback_comp {S X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : S ⟶ X) (g : X ⟶ Y) (n : ℕ)
    (a : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) Y n) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n g a) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n (f ≫ g) a := by
  unfold Betti.Scheme.schemeBettiMap
  rw [Functor.map_comp, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp]
  rfl

/-- Pullback by the product map is exactly the four factors used in ThetaCycle. -/
theorem productMap_fourCup {A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    {π : ∀ i, X.toOver ⟶ (A i).toOver}
    (hproduct : IsLimit (Fan.mk X.toOver π))
    (f : ∀ i, S.toOver ⟶ (A i).toOver)
    (e : ∀ i, (A i).variety.complexCohomology 1) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 4 (productMap hproduct f)
      (fourCup X (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i) (e i))) =
      fourCup S (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f i) (e i)) := by
  rw [schemePullback_fourCup]
  simp only [schemePullback_comp, productMap_proj]

/-- Full Functoriality proper-pushforward compatibility, repeated as a proposition
so the committed unproved statement need not be imported or invoked. -/
def ProperCycleClassCompatibility : Prop :=
  ∀ {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : S.toOver ⟶ X.toOver)
    (hf : IsProper f.left) (p q : ℕ)
    (hdeg : p + X.complexDimension = q + S.complexDimension)
    (z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle S p),
    X.geometricCycleClassMap q (Cycles.Functoriality.UnitCap.cyclePushforward f hf p q hdeg z) =
      Cycles.Functoriality.UnitCap.cohomologyPushforward f hf p q hdeg (S.geometricCycleClassMap p z)

/-- The whole source is an actual rational algebraic cycle. -/
def fullCycle (S : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle S 0 :=
  Finsupp.single (Cycles.Functoriality.Support.Construction.fullCycleSupport S) 1

theorem fullCycle_class (S : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    S.geometricCycleClassMap 0 (fullCycle S) = Cycles.Functoriality.UnitCap.cohomologyUnit S := by
  rw [fullCycle, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single,
    one_smul, Cycles.Functoriality.SupportClass.Construction.fullCycleSupport_geometricCycleClass]

/-- The actual algebraic pushforward, with its function-field multiplicities. -/
def pushedCycle {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : S.toOver ⟶ X.toOver) (q : ℕ)
    (hdeg : 0 + X.complexDimension = q + S.complexDimension) :
    CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X q :=
  Cycles.Functoriality.UnitCap.cyclePushforward f (map_isProper f) 0 q hdeg (fullCycle S)

theorem pushedCycle_class (hFunctoriality : ProperCycleClassCompatibility)
    {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : S.toOver ⟶ X.toOver) (q : ℕ)
    (hdeg : 0 + X.complexDimension = q + S.complexDimension) :
    X.geometricCycleClassMap q (pushedCycle f q hdeg) =
      Cycles.Functoriality.UnitCap.cohomologyPushforward f (map_isProper f) 0 q hdeg
        (Cycles.Functoriality.UnitCap.cohomologyUnit S) := by
  rw [pushedCycle, hFunctoriality, fullCycle_class]

/-- Canonical complex orientation, with rational coefficients. -/
def fundamentalQ (S : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace S.toOver)).homology
      (2 * S.complexDimension) :=
  AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ)
    (TopCat.of S.analyticSpace) (2 * S.complexDimension)
    (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass S.complexDimension S.analyticSpace)

/-- The Poincare dual of the algebraic pushed cycle is the image of the
source's actual oriented fundamental class. -/
theorem pushedCycle_poincare (hFunctoriality : ProperCycleClassCompatibility)
    {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : S.toOver ⟶ X.toOver) (q : ℕ)
    (hdeg : 0 + X.complexDimension = q + S.complexDimension) :
    (X.poincareDuality (q + q) (2 * S.complexDimension) (by omega)).hom
      (X.geometricCycleClassMap q (pushedCycle f q hdeg)) =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
        (2 * S.complexDimension) (fundamentalQ S) := by
  rw [pushedCycle_class hFunctoriality,
    Cycles.Functoriality.UnitCap.cohomologyPushforward_eq_poincare f (map_isProper f) 0 q hdeg (Nat.zero_le _)]
  change (X.poincareDuality (q + q) (2 * S.complexDimension) _).hom
    ((X.poincareDuality (q + q) (2 * S.complexDimension) _).inv
      (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
        (2 * S.complexDimension)
        ((S.poincareDuality 0 (2 * S.complexDimension) _).hom
          (Cycles.Functoriality.UnitCap.cohomologyUnit S)))) = _
  erw [Iso.inv_hom_id_apply, Cycles.Functoriality.UnitProjection.Construction.poincareUnit_eq_rationalFundamental]
  rfl

/-- Evaluation on the pushed geometric cycle is evaluation of the
pullback on the canonical fundamental class, for rational test classes. -/
theorem pushedCycle_evaluation (hFunctoriality : ProperCycleClassCompatibility)
    {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : S.toOver ⟶ X.toOver) (q : ℕ)
    (hdeg : 0 + X.complexDimension = q + S.complexDimension)
    (a : X.rationalCohomology (2 * S.complexDimension)) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace X.toOver)
      (2 * S.complexDimension) a
      ((X.poincareDuality (q + q) (2 * S.complexDimension) (by omega)).hom
        (X.geometricCycleClassMap q (pushedCycle f q hdeg))) =
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace S.toOver)
        (2 * S.complexDimension)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * S.complexDimension) f a)
        (fundamentalQ S) := by
  rw [pushedCycle_poincare hFunctoriality]
  exact (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) (2 * S.complexDimension) a (fundamentalQ S)).symm

/-- Naturality of complex Betti evaluation on rational homology.
The scalar-restriction comparison is canonical. -/
theorem complexRationalEvaluation_naturality {S X : TopCat.{0}}
    (f : S ⟶ X) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) S).homology n) :
    ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology S n
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n a) z =
      ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology X n a
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f n z) := by
  have hc : (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso S n).inv
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n a) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℂ) f n
        ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv a) := by
    apply (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso S n).toLinearEquiv.injective
    change (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso S n).hom
      ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso S n).inv _) =
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso S n).hom _
    erw [Iso.inv_hom_id_apply]
    have h := ConcreteCategory.congr_hom
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso_naturality f n)
      ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv a)
    change (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso S n).hom
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℂ) f n
        ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv a)) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n
        ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).hom
          ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv a)) at h
    erw [Iso.inv_hom_id_apply] at h
    exact h.symm
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℂ) S n
    ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso S n).inv
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n a)) z = _
  rw [hc]
  exact AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℂ) f n
    ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv a) z

/-- The same canonical class transported only along an equality of degrees. -/
def fundamentalQInDegree (S : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (hn : 2 * S.complexDimension = n) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace S.toOver)).homology n :=
  cast (congrArg (fun k =>
    ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace S.toOver)).homology k : Type)) hn)
      (fundamentalQ S)

theorem pushedCycle_poincare_inDegree (hFunctoriality : ProperCycleClassCompatibility)
    {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : S.toOver ⟶ X.toOver) (q : ℕ)
    (hdeg : 0 + X.complexDimension = q + S.complexDimension)
    (n : ℕ) (hn : 2 * S.complexDimension = n)
    (hdual : (q + q) + n = 2 * X.complexDimension) :
    (X.poincareDuality (q + q) n hdual).hom
      (X.geometricCycleClassMap q (pushedCycle f q hdeg)) =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) n
        (fundamentalQInDegree S n hn) := by
  cases hn
  exact pushedCycle_poincare hFunctoriality f q hdeg

/-- The actual pushed algebraic surface evaluates the fourfold tensor by
its geometric fundamental-class pairing. No arbitrary integration functional
is introduced. -/
theorem pushedSurface_fourCup_evaluation
    (hFunctoriality : ProperCycleClassCompatibility)
    {A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (hS : S.complexDimension = 2)
    {π : ∀ i, X.toOver ⟶ (A i).toOver}
    (hproduct : IsLimit (Fan.mk X.toOver π))
    (f : ∀ i, S.toOver ⟶ (A i).toOver)
    (q : ℕ) (hdeg : 0 + X.complexDimension = q + S.complexDimension)
    (e : ∀ i, (A i).variety.complexCohomology 1) :
    ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (Betti.Scheme.schemePointSpace X.toOver) 4
      (fourCup X (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i) (e i)))
      ((X.poincareDuality (q + q) 4 (by omega)).hom
        (X.geometricCycleClassMap q (pushedCycle (productMap hproduct f) q hdeg))) =
      ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (Betti.Scheme.schemePointSpace S.toOver) 4
        (fourCup S (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f i) (e i)))
        (fundamentalQInDegree S 4 (by omega)) := by
  rw [pushedCycle_poincare_inDegree hFunctoriality (productMap hproduct f) q hdeg 4
    (by omega) (by omega)]
  rw [← complexRationalEvaluation_naturality]
  change ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (Betti.Scheme.schemePointSpace S.toOver) 4
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 4 (productMap hproduct f) _) _ = _
  rw [productMap_fourCup]

/-- A genuine nonzero surface pairing gives a nonzero fourfold tensor
and a nonzero algebraic pushed-cycle class. -/
theorem pushedSurface_nonzero
    (hFunctoriality : ProperCycleClassCompatibility)
    {A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (hS : S.complexDimension = 2)
    {π : ∀ i, X.toOver ⟶ (A i).toOver}
    (hproduct : IsLimit (Fan.mk X.toOver π))
    (f : ∀ i, S.toOver ⟶ (A i).toOver)
    (q : ℕ) (hdeg : 0 + X.complexDimension = q + S.complexDimension)
    (e : ∀ i, (A i).variety.complexCohomology 1)
    (hnonzero : ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (Betti.Scheme.schemePointSpace S.toOver) 4
      (fourCup S (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f i) (e i)))
      (fundamentalQInDegree S 4 (by omega)) ≠ 0) :
    fourCup X (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i) (e i)) ≠ 0 ∧
      X.geometricCycleClassMap q (pushedCycle (productMap hproduct f) q hdeg) ≠ 0 := by
  rw [← pushedSurface_fourCup_evaluation hFunctoriality hS hproduct f q hdeg e] at hnonzero
  constructor
  · intro hz
    rw [hz, map_zero] at hnonzero
    exact hnonzero rfl
  · intro hz
    rw [hz] at hnonzero
    erw [map_zero, map_zero] at hnonzero
    exact hnonzero rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionQ.CM
