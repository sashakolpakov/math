import OAI.AlgebraicTopology.Cohomology.Singular.RationalComplex
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Coefficient Restriction -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.CoefficientRestriction.CM

noncomputable section

/-!
# Coefficient naturality of scalar restriction

The cochain and cohomology comparison maps commute with maps of coefficients.
In particular multiplication on complex coefficients becomes multiplication
on ordinary complex cohomology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

variable {R S : Type} [CommRing R] [CommRing S]

/-- Restricting scalars in singular cochains commutes with coefficient maps. -/
theorem singularCochainsRestrictScalarsIso_coefficient (f : R →+* S)
    {M N : ModuleCat.{0} S} (g : M ⟶ N) (X : TopCat.{0}) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X) ≫ (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f N X).hom =
      (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M X).hom ≫
        AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap ((ModuleCat.restrictScalars f).map g) X := by
  let F := ModuleCat.restrictScalars.{0} f
  ext n : 1
  apply Quiver.Hom.op_inj
  change sigmaComparison F.op (fun _ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n => op N) ≫
      F.op.map (CategoryTheory.Limits.Sigma.map (fun _ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n => g.op)) =
    CategoryTheory.Limits.Sigma.map (fun _ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n => (F.map g).op) ≫
      sigmaComparison F.op (fun _ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n => op M)
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro s
  erw [ι_comp_sigmaComparison_assoc, ← Functor.map_comp, Sigma.ι_map,
    Functor.map_comp, Sigma.ι_map_assoc]
  exact (congrArg (fun k => F.op.map g.op ≫ k)
    (ι_comp_sigmaComparison F.op (fun _ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n => op M) s)).symm

/-- Restriction of scalars in genuine singular cohomology is natural in
coefficients as well as in the underlying space. -/
theorem singularCohomologyRestrictScalarsIso_coefficient (f : R →+* S)
    {M N : ModuleCat.{0} S} (g : M ⟶ N) (X : TopCat.{0}) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap ((ModuleCat.restrictScalars f).map g) X n ≫
        (AlgebraicTopology.Cohomology.Singular.Chains.singularCohomologyRestrictScalarsIso f N X n).hom =
      (AlgebraicTopology.Cohomology.Singular.Chains.singularCohomologyRestrictScalarsIso f M X n).hom ≫
        (ModuleCat.restrictScalars f).map (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap g X n) := by
  let F := ModuleCat.restrictScalars.{0} f
  let FM := AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M X
  let FN := AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f N X
  have hci : AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap (F.map g) X ≫ FN.inv =
      FM.inv ≫ (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X) := by
    apply (cancel_mono FN.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [show (F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X) ≫ FN.hom =
      FM.hom ≫ AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap (F.map g) X from
        singularCochainsRestrictScalarsIso_coefficient f g X]
    simp
  have hb := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} S)
      (ComplexShape.up ℕ) n).map (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X)) F
  change HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X)) n ≫
        (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).sc n).mapHomologyIso F).hom =
      (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).sc n).mapHomologyIso F).hom ≫
        F.map (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X) n) at hb
  change HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap (F.map g) X) n ≫
      (HomologicalComplex.homologyMap FN.inv n ≫
        (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).sc n).mapHomologyIso F).hom) =
    (HomologicalComplex.homologyMap FM.inv n ≫
        (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).sc n).mapHomologyIso F).hom) ≫
      F.map (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X) n)
  erw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, hci,
    HomologicalComplex.homologyMap_comp, Category.assoc, hb]
  change HomologicalComplex.homologyMap FM.inv n ≫
      ((((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).sc n).mapHomologyIso F).hom ≫
        F.map (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X) n)) = _
  exact (Category.assoc _ _ _).symm

/-- Scaling scalar coefficients induces the ordinary scaling of cohomology. -/
theorem coefficientMap_scalar (F : Type) [Field F] (a : F)
    (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of F F) X n) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap (ModuleCat.ofHom (a • LinearMap.id : F →ₗ[F] F)) X n c =
      a • c := by
  apply (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n).injective
  ext z
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of F F) X n _ z =
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of F F) X n (a • c) z
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_coefficient]
  simp only [map_smul, LinearMap.smul_apply]
  rfl

/-- Coefficient multiplication commutes with the canonical comparison from
complex-valued rational cohomology to ordinary complex cohomology. -/
theorem complexCohomologyRestrictionIso_scalar (a : ℂ) (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℂ) X n) :
    (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).hom
      (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap (ModuleCat.ofHom
        ((a • LinearMap.id : ℂ →ₗ[ℂ] ℂ).restrictScalars ℚ)) X n c) =
      a • (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).hom c := by
  let g : ModuleCat.of ℂ ℂ ⟶ ModuleCat.of ℂ ℂ :=
    ModuleCat.ofHom (a • LinearMap.id)
  let F := ModuleCat.restrictScalars (algebraMap ℚ ℂ)
  have hg : ModuleCat.ofHom
        ((a • LinearMap.id : ℂ →ₗ[ℂ] ℂ).restrictScalars ℚ) ≫
      AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom =
    AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom ≫ F.map g := by
    ext z
    rfl
  have h := singularCohomologyRestrictScalarsIso_coefficient
    (algebraMap ℚ ℂ) g X n
  have hc := ConcreteCategory.congr_hom h
    (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom X n c)
  change (AlgebraicTopology.Cohomology.Singular.Chains.singularCohomologyRestrictScalarsIso (algebraMap ℚ ℂ)
      (ModuleCat.of ℂ ℂ) X n).hom
      (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap (F.map g) X n
        (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom X n c)) =
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap g X n
      ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).hom c) at hc
  have hc' := hc.trans (coefficientMap_scalar ℂ a X n
    ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).hom c))
  change (AlgebraicTopology.Cohomology.Singular.Chains.singularCohomologyRestrictScalarsIso (algebraMap ℚ ℂ)
      (ModuleCat.of ℂ ℂ) X n).hom
      (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom X n
        (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap _ X n c)) = _
  have hh := congrArg (fun k => AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap k X n) hg
  rw [AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap_comp, AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap_comp] at hh
  exact (congrArg (AlgebraicTopology.Cohomology.Singular.Chains.singularCohomologyRestrictScalarsIso (algebraMap ℚ ℂ)
    (ModuleCat.of ℂ ℂ) X n).hom (ConcreteCategory.congr_hom hh c)).trans hc'

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.CoefficientRestriction.CM
