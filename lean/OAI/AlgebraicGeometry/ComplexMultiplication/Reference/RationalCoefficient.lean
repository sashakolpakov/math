import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.ConcreteRationalNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.SingularPresheafConstants
import OAI.AlgebraicGeometry.ComplexMultiplication.CMComparisonTo

/-! # Rational Coefficient -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficient

noncomputable section

section

/-! # Actual coefficient inclusion in the original singular presheaf complex -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite OAI.AlgebraicTopology.Singular

/-- The actual native singular presheaf complex, with its module scalars forgotten. -/
abbrev additiveSingularPresheafComplex (R : Type) [CommRing R] (Y : TopCat.{0}) :=
  (Functor.mapHomologicalComplex
    ((Functor.whiskeringRight (Opens Y)ᵒᵖ (ModuleCat R) AddCommGrpCat).obj
      (forget₂ (ModuleCat R) AddCommGrpCat)) (ComplexShape.up ℕ)).obj
        (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of R R) Y)

set_option backward.isDefEq.respectTransparency false in
/-- Cast every actual local rational simplex value into ℂ. -/
def actualAdditiveRationalToComplexPresheafMap (Y : TopCat.{0}) :
    additiveSingularPresheafComplex ℚ Y ⟶ additiveSingularPresheafComplex ℂ Y where
  f n :=
    { app U := (Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap (TopCat.of U.unop)).f n
      naturality {U V} i := by
        exact congrArg (fun h => h.f n)
          (Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap_naturality
            ((Opens.toTopCat Y).map i.unop)) }
  comm' i j _ := by
    apply NatTrans.ext
    funext U
    exact (Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap (TopCat.of U.unop)).comm i j

/-- Actual chain evaluation puts coefficient inclusion in the unchanged original complex. -/
def originalRationalToComplexSingularPresheafMap (Y : TopCat.{0}) :
    AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex ℚ Y ⟶ AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex ℂ Y :=
  (SingularPresheafBridge.singularPresheafComplexBridgeIso ℚ Y).inv ≫
    actualAdditiveRationalToComplexPresheafMap Y ≫
      (SingularPresheafBridge.singularPresheafComplexBridgeIso ℂ Y).hom

set_option backward.isDefEq.respectTransparency false in
/-- The original comparison square uses the actual local coefficient map. -/
theorem originalRationalToComplexSingularPresheafMap_square (Y : TopCat.{0}) :
    (SingularPresheafBridge.singularPresheafComplexBridgeIso ℚ Y).hom ≫
        originalRationalToComplexSingularPresheafMap Y =
      actualAdditiveRationalToComplexPresheafMap Y ≫
        (SingularPresheafBridge.singularPresheafComplexBridgeIso ℂ Y).hom := by
  simp only [originalRationalToComplexSingularPresheafMap, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

end

section

/-! # Coefficient inclusion retains the original constant augmentation -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite OAI.AlgebraicTopology.Singular
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false in
/-- The inverse original comparison evaluates a constant zero-cochain to its actual constant. -/
theorem originalConstantZeroCochain_evaluation (R : Type) [CommRing R]
    (Y : TopCat.{0}) (U : (Opens Y)ᵒᵖ) (r : R)
    (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (TopCat.of U.unop) 0) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (TopCat.of U.unop)) (ModuleCat.of R R) s
      ((SingularCochainBridge.singularCochainBridgeIso R (TopCat.of U.unop)).inv.f 0
        (AlgebraicTopology.Singular.SheafCochain.constantSingularZeroCochain R Y U r)) = r := by
  let K := TopCat.toSSet.obj (TopCat.of U.unop)
  let ψ := AlgebraicTopology.Singular.SheafCochain.constantSingularZeroCochain R Y U r
  have hi := congrArg (fun h => h.f 0)
    (SingularCochainBridge.singularCochainBridgeIso R (TopCat.of U.unop)).inv_hom_id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hi
  have hv := congrArg
    (fun (φ : Module.Dual R ((K.chainComplex (ModuleCat.of R R)).X 0)) =>
      φ (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain K s)) (ConcreteCategory.congr_hom hi ψ)
  change AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K (ModuleCat.of R R) 0
      ((SingularCochainBridge.singularCochainBridgeIso R (TopCat.of U.unop)).inv.f 0 ψ)
        (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain K s) = r * (AlgebraicTopology.Singular.SheafCochain.simplicialZeroAugmentation R K).hom (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain K s) at hv
  rw [AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex, SingularPresheafConstants.originalZeroAugmentation_simplex, mul_one] at hv
  exact hv

set_option backward.isDefEq.respectTransparency false in
/-- Actual coefficient inclusion casts the evaluated value, after literal additive forgetting. -/
theorem actualAdditiveRationalToComplexCochainMap_evaluation (Y : TopCat.{0})
    {n : ℕ} (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) Y).X n) (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices Y n) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Y) (ModuleCat.of ℂ ℂ) s
        ((Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap Y).f n c) =
      algebraMap ℚ ℂ (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj Y) (ModuleCat.of ℚ ℚ) s c) := by
  exact ConcreteCategory.congr_hom (ConcreteRationalCoefficientCochains.actualRationalToComplexCochainMap_evaluation Y s) c

set_option backward.isDefEq.respectTransparency false in
/-- The original constant augmentation commutes with the genuine rational-to-complex coefficient map. -/
theorem originalRationalToComplexSingularPresheafMap_constants (Y : TopCat.{0}) :
    AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero ℚ Y ≫
        (originalRationalToComplexSingularPresheafMap Y).f 0 =
      (Functor.const (Opens Y)ᵒᵖ).map
        (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom) ≫
          AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero ℂ Y := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro q
  change ℚ at q
  let K := TopCat.toSSet.obj (TopCat.of U.unop)
  change AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K (ModuleCat.of ℂ ℂ) 0
      ((Coefficient.ConcreteRationalNaturality.actualAdditiveRationalToComplexCochainMap (TopCat.of U.unop)).f 0
        ((SingularCochainBridge.singularCochainBridgeIso ℚ (TopCat.of U.unop)).inv.f 0
          (AlgebraicTopology.Singular.SheafCochain.constantSingularZeroCochain ℚ Y U q))) =
    (algebraMap ℚ ℂ q) • (AlgebraicTopology.Singular.SheafCochain.openZeroAugmentation ℂ Y U).hom
  apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext K (ModuleCat.of ℂ ℂ)
  intro s
  rw [AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex,
    actualAdditiveRationalToComplexCochainMap_evaluation, originalConstantZeroCochain_evaluation]
  change algebraMap ℚ ℂ q = algebraMap ℚ ℂ q *
    (AlgebraicTopology.Singular.SheafCochain.simplicialZeroAugmentation ℂ K).hom (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain K s)
  rw [SingularPresheafConstants.originalZeroAugmentation_simplex, mul_one]

end

/-! # The original coefficient inclusion square on the full sheaf resolutions -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace OAI.AlgebraicTopology.Singular

/-- Sheafify the actual local rational-to-complex coefficient map. -/
def originalRationalToComplexSingularSheafMap (Y : TopCat.{0}) :
    AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ Y ⟶ AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℂ Y :=
  ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (originalRationalToComplexSingularPresheafMap Y)

set_option backward.isDefEq.respectTransparency false in
/-- Sheafification retains the original constant-augmentation coefficient square. -/
theorem originalRationalToComplexSingularSheafMap_constants_zero (Y : TopCat.{0}) :
    AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf ℚ Y ≫
        (originalRationalToComplexSingularSheafMap Y).f 0 =
      (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).map
        (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom) ≫
          AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf ℂ Y := by
  let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat
  change S.map (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero ℚ Y) ≫
      S.map ((originalRationalToComplexSingularPresheafMap Y).f 0) =
    S.map ((Functor.const (Opens Y)ᵒᵖ).map
      (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom)) ≫
        S.map (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZero ℂ Y)
  rw [← Functor.map_comp, ← Functor.map_comp,
    originalRationalToComplexSingularPresheafMap_constants]

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient square holds for the whole original nonnegative resolution. -/
theorem originalRationalToComplexSingularSheafMap_constants (Y : TopCat.{0}) :
    AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex ℚ Y ≫
        originalRationalToComplexSingularSheafMap Y =
      (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat Y)).map
        ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).map
          (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom)) ≫
            AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex ℂ Y := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf ℚ Y ≫
          (originalRationalToComplexSingularSheafMap Y).f 0 =
        (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).map
          (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom) ≫
            AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainZeroSheaf ℂ Y
      exact originalRationalToComplexSingularSheafMap_constants_zero Y
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
        ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℚ))
        (n + 1) (Nat.succ_ne_zero n)).eq_of_src _ _

variable (X : Over (Spec (.of ℂ)))

/-- Extend the same genuine coefficient map by zero into integer degrees. -/
def originalRationalToComplexSingularSheafIntMap :
    ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℚ ⟶ ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℂ :=
  HomologicalComplex.extendMap
    (originalRationalToComplexSingularSheafMap (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
      ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
/-- Exact compatibility with the original rational constant-sheaf coefficient map. -/
theorem originalRationalToComplexSingularSheafIntMap_constants :
    ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℚ ≫
        originalRationalToComplexSingularSheafIntMap X =
      ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X ≫ ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℂ := by
  unfold originalRationalToComplexSingularSheafIntMap ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt
    ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    originalRationalToComplexSingularSheafMap_constants]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficient
