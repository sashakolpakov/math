import OAI.AlgebraicGeometry.AbelianVariety.CupGeneration
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.CMCore
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! # Exterior Cohomology Complex Cup -/

namespace OAI.AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup.Constructions

noncomputable section

section

open scoped TensorProduct

/-- The cup-normalized rational isomorphism after the canonical extension of coefficients. -/
def complexExteriorCupEquiv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    ℂ ⊗[ℚ] (⋀[ℚ]^n (A.variety.rationalCohomology 1)) ≃ₗ[ℂ]
      A.variety.complexCohomology n := by
  let : Module.Finite ℚ (A.variety.rationalCohomology n) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety n
  exact (LinearEquiv.baseChange ℚ ℂ _ _ (CupGeneration.Constructions.ExteriorCohomology.rationalExteriorCupEquiv A n)).trans
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (Betti.Scheme.schemePointSpace A.toOver) n)

theorem complexExteriorCupEquiv_apply (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (x : ℂ ⊗[ℚ] (⋀[ℚ]^n (A.variety.rationalCohomology 1))) :
    complexExteriorCupEquiv A n x =
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) n
        ((CupMap.Constructions.ExteriorCohomology.exteriorCup A n).baseChange ℂ x) := rfl

/-- The complex exterior algebra of actual complexified rational H¹ maps isomorphically to Betti cohomology. -/
def complexH1ExteriorCupEquiv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    (⋀[ℂ]^n (ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1))) ≃ₗ[ℂ]
      A.variety.complexCohomology n :=
  (ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ (A.variety.rationalCohomology 1) n).symm.trans
    (complexExteriorCupEquiv A n)

end

section

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial
open OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

variable {R S : Type} [CommRing R] [CommRing S]

def restrictCocycle (f : R →+* S) (K : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n :=
  ⟨c.val, c.property⟩

theorem restrictCocycle_class (f : R →+* S) (K : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K n) :
    ((K.sc n).mapHomologyIso (ModuleCat.restrictScalars f)).hom
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (((ModuleCat.restrictScalars f).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) n (restrictCocycle f K n c)) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K n c := by
  let F := ModuleCat.restrictScalars f
  let K' := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let h := (K.sc n).moduleCatLeftHomologyData
  let h' := h.map F
  let c' := restrictCocycle f K n c
  let z := (K'.sc n).moduleCatCyclesIso.inv c'
  have hz : h'.cyclesIso.hom z = c := by
    have hi := ConcreteCategory.congr_hom h'.cyclesIso_hom_comp_i z
    have hz' := ConcreteCategory.congr_hom (K'.sc n).moduleCatCyclesIso_inv_iCycles c'
    change (h'.i) (h'.cyclesIso.hom z) = (K'.sc n).iCycles z at hi
    change (K'.sc n).iCycles z = c.val at hz'
    apply Subtype.ext
    exact hi.trans hz'
  have hπ := ConcreteCategory.congr_hom h'.homologyπ_comp_homologyIso_hom z
  change h'.homologyIso.hom ((K'.sc n).homologyπ z) = h'.π (h'.cyclesIso.hom z) at hπ
  rw [hz] at hπ
  rw [h.mapHomologyIso_eq F]
  change (F.map h.homologyIso.inv)
    (h'.homologyIso.hom (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K' n c')) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K n c
  rw [AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_homologyπ]
  exact congrArg (F.map h.homologyIso.inv) hπ

theorem simplicialRestriction_evaluation (f : R →+* S) (K : SSet.{0})
    (M : ModuleCat.{0} S) {n : ℕ} (s : K _⦋n⦌) :
    (AlgebraicTopology.Cohomology.Singular.Chains.simplicialCochainsRestrictScalarsIso f K M).hom.f n ≫
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K ((ModuleCat.restrictScalars f).obj M) s =
        (ModuleCat.restrictScalars f).map (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation K M s) := by
  let F := ModuleCat.restrictScalars f
  apply Quiver.Hom.op_inj
  change Sigma.ι (fun _ : K _⦋n⦌ => F.op.obj (op M)) s ≫
    sigmaComparison F.op (fun _ : K _⦋n⦌ => op M) =
      F.op.map (Sigma.ι (fun _ : K _⦋n⦌ => op M) s)
  exact ι_comp_sigmaComparison F.op (fun _ : K _⦋n⦌ => op M) s

def restrictedSingularCocycle (f : R →+* S) (M : ModuleCat.{0} S) (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M X n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles ((ModuleCat.restrictScalars f).obj M) X n :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M X).hom n
    (restrictCocycle f (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) n c)

theorem restrictedSingularCocycle_evaluation (f : R →+* S) (M : ModuleCat.{0} S)
    (X : TopCat.{0}) (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M X n) (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) ((ModuleCat.restrictScalars f).obj M) s
      (restrictedSingularCocycle f M X n c).val =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M s c.val :=
  ConcreteCategory.congr_hom (simplicialRestriction_evaluation f (TopCat.toSSet.obj X) M s) c.val

theorem restrictedSingularCocycle_class (f : R →+* S) (M : ModuleCat.{0} S)
    (X : TopCat.{0}) (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M X n) :
    (AlgebraicTopology.Cohomology.Singular.Chains.singularCohomologyRestrictScalarsIso f M X n).hom
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass ((ModuleCat.restrictScalars f).obj M) X n
        (restrictedSingularCocycle f M X n c)) = AlgebraicTopology.Cohomology.Singular.Representatives.singularClass M X n c := by
  let F := ModuleCat.restrictScalars f
  let e := AlgebraicTopology.Cohomology.Singular.Chains.singularCochainsRestrictScalarsIso f M X
  let c' := restrictCocycle f (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) n c
  change (((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).sc n).mapHomologyIso F).hom
    (HomologicalComplex.homologyMap e.inv n
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (F.obj M) X) n (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap e.hom n c'))) = _
  rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp, e.hom_inv_id,
    HomologicalComplex.homologyMap_id, ConcreteCategory.id_apply]
  exact restrictCocycle_class f (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X) n c

end

section

open _root_.CategoryTheory
open scoped Simplicial
open OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

/-- A complex cocycle as a complex-valued rational cocycle, with unchanged simplex values. -/
def complexCocycleAsRational (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℂ ℂ) X n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℂ) X n :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.inv X) n
    (restrictedSingularCocycle (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X n c)

theorem coefficientCocycle_evaluation {R : Type} [CommRing R] {M N : ModuleCat.{0} R}
    (f : M ⟶ N) (X : TopCat.{0}) (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M X n)
    (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) N s
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap f X n c).val =
      f (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M s c.val) :=
  ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_evaluation f X s) c.val

theorem complexCocycleAsRational_evaluation (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℂ ℂ) X n) (s : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices X n) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℂ) s
      (complexCocycleAsRational X n c).val =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) s c.val := by
  unfold complexCocycleAsRational
  rw [coefficientCocycle_evaluation, restrictedSingularCocycle_evaluation]
  rfl

theorem complexCocycleAsRational_class (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℂ ℂ) X n) :
    (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).hom
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℂ) X n (complexCocycleAsRational X n c)) =
      AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℂ ℂ) X n c := by
  change (AlgebraicTopology.Cohomology.Singular.Chains.singularCohomologyRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X n).hom
    (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom X n
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℂ) X n
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.inv X n
          (restrictedSingularCocycle (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X n c)))) = _
  rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class]
  have hcancel : AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.inv X n ≫
      AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.hom X n = 𝟙 _ := by
    rw [← AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap_comp, AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCoefficientsRestrictionIso.inv_hom_id, AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap_id]
  have hval := ConcreteCategory.congr_hom hcancel
    (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass _ X n (restrictedSingularCocycle (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X n c))
  exact (congrArg
    (AlgebraicTopology.Cohomology.Singular.Chains.singularCohomologyRestrictScalarsIso (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X n).hom
    hval).trans (restrictedSingularCocycle_class (algebraMap ℚ ℂ) (ModuleCat.of ℂ ℂ) X n c)

theorem complexCocycleAsRational_cup (X : TopCat.{0}) (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℂ ℂ) X p)
    (d : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℂ ℂ) X q) :
    complexCocycleAsRational X (p + q)
      (AlgebraicTopology.Products.CupCohomology.cocycleCupWith (TopCat.toSSet.obj X) (LinearMap.mul ℂ ℂ) p q c d) =
      AlgebraicTopology.Products.CupCohomology.cocycleCupWith (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℂ) p q
        (complexCocycleAsRational X p c) (complexCocycleAsRational X q d) := by
  apply Subtype.ext
  apply AlgebraicTopology.Products.Cup.cochain_ext (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℂ)
  intro s
  rw [complexCocycleAsRational_evaluation, AlgebraicTopology.Products.CupCohomology.cocycleCupWith_val, AlgebraicTopology.Products.Cup.evaluation_cupWith,
    AlgebraicTopology.Products.CupCohomology.cocycleCupWith_val, AlgebraicTopology.Products.Cup.evaluation_cupWith,
    complexCocycleAsRational_evaluation, complexCocycleAsRational_evaluation]
  rfl

theorem complexCohomologyRestrictionIso_cup (X : TopCat.{0}) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℂ) X p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℂ) X q) :
    (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X (p + q)).hom
      (AlgebraicTopology.Products.CupCohomology.cohomologyCupWith (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℂ) p q a b) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) X p q
        ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X p).hom a)
        ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X q).hom b) := by
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℂ ℂ) X p
    ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X p).hom a)
  obtain ⟨d, hd⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℂ ℂ) X q
    ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X q).hom b)
  have ha := (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X p).toLinearEquiv.injective
    ((complexCocycleAsRational_class X p c).trans hc)
  have hb := (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X q).toLinearEquiv.injective
    ((complexCocycleAsRational_class X q d).trans hd)
  rw [← ha, ← hb, AlgebraicTopology.Products.CupCohomology.cohomologyCupWith_class_class, ← complexCocycleAsRational_cup,
    complexCocycleAsRational_class, complexCocycleAsRational_class,
    complexCocycleAsRational_class, AlgebraicTopology.Products.CupCohomology.singularCohomologyCup_class_class]

theorem rationalInclusion_cocycleCup (X : TopCat.{0}) (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X p)
    (d : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X q) :
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X (p + q)
      (AlgebraicTopology.Products.CupCohomology.cocycleCupWith (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℚ) p q c d) =
      AlgebraicTopology.Products.CupCohomology.cocycleCupWith (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℂ) p q
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X p c)
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X q d) := by
  apply Subtype.ext
  apply AlgebraicTopology.Products.Cup.cochain_ext (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℂ)
  intro s
  rw [coefficientCocycle_evaluation, AlgebraicTopology.Products.CupCohomology.cocycleCupWith_val, AlgebraicTopology.Products.Cup.evaluation_cupWith,
    AlgebraicTopology.Products.CupCohomology.cocycleCupWith_val, AlgebraicTopology.Products.Cup.evaluation_cupWith,
    coefficientCocycle_evaluation, coefficientCocycle_evaluation]
  exact Rat.cast_mul _ _

theorem rationalInclusion_cup (X : TopCat.{0}) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X (p + q)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X p q a b) =
      AlgebraicTopology.Products.CupCohomology.cohomologyCupWith (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℂ) p q
        (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X p a)
        (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X q b) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X p a
  obtain ⟨d, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X q b
  rw [AlgebraicTopology.Products.CupCohomology.singularCohomologyCup_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class, rationalInclusion_cocycleCup,
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class, AlgebraicTopology.Products.CupCohomology.cohomologyCupWith_class_class]

/-- The canonical rational-to-complex coefficient map preserves actual cup products. -/
theorem rationalToComplex_cup (X : TopCat.{0}) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q) :
    AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X (p + q) (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X p q a b) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) X p q
        (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X p a) (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X q b) := by
  change (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X (p + q)).hom
    (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X (p + q)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X p q a b)) = _
  rw [rationalInclusion_cup]
  exact complexCohomologyRestrictionIso_cup X p q _ _

theorem rationalToComplex_cupUnit (X : TopCat.{0}) :
    AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := ℚ) X) =
      AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := ℂ) X := by
  have hc : AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X 0
      (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (R := ℚ) (TopCat.toSSet.obj X)) =
      complexCocycleAsRational X 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (R := ℂ) (TopCat.toSSet.obj X)) := by
    apply Subtype.ext
    apply AlgebraicTopology.Products.Cup.cochain_ext (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℂ)
    intro s
    rw [coefficientCocycle_evaluation, complexCocycleAsRational_evaluation]
    change AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion
      (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) s
        (AlgebraicTopology.Products.Cup.cupUnit (TopCat.toSSet.obj X))) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) s
        (AlgebraicTopology.Products.Cup.cupUnit (TopCat.toSSet.obj X))
    rw [AlgebraicTopology.Products.Cup.evaluation_cupUnit, AlgebraicTopology.Products.Cup.evaluation_cupUnit]
    exact Rat.cast_one
  change (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X 0).hom
    (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap (ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion) X 0
      (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (TopCat.toSSet.obj X)))) = _
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class, hc]
  exact complexCocycleAsRational_class X 0 _

end

open scoped TensorProduct
open OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality OAI.AlgebraicGeometry.ComplexMultiplication.CMCore.CM

/-- Iterated ordinary complex cup products, as multilinear maps. -/
def complexH1CupMultilinear (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    (n : ℕ) → MultilinearMap ℂ (fun _ : Fin n => A.variety.complexCohomology 1)
      (A.variety.complexCohomology n)
  | 0 => MultilinearMap.constOfIsEmpty ℂ _
      (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (Betti.Scheme.schemePointSpace A.toOver))
  | n + 1 =>
      ((AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) n 1).compMultilinearMap
        (complexH1CupMultilinear A n)).uncurryRight

theorem complexH1Cup_of_rational (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (v : Fin n → A.variety.rationalCohomology 1) :
    Constructions.complexH1CupMultilinear A n
      (fun i => AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) 1 (v i)) =
      AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) n (A.rationalH1Cup n v) := by
  induction n with
  | zero => exact (rationalToComplex_cupUnit _).symm
  | succ n ih =>
    change AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) n 1
      (Constructions.complexH1CupMultilinear A n
        (fun i => AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) 1 (Fin.init v i)))
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) 1 (v (Fin.last n))) = _
    rw [ih]
    exact (rationalToComplex_cup _ n 1 _ _).symm

theorem complexH1ExteriorCup_rational_wedge (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (v : Fin n → A.variety.rationalCohomology 1) :
    complexH1ExteriorCupEquiv A n
      (exteriorPower.ιMulti ℂ n (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i)) =
      AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace A.toOver) n (A.rationalH1Cup n v) := by
  have he : (ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ (A.variety.rationalCohomology 1) n).symm
      (exteriorPower.ιMulti ℂ n (fun i => (1 : ℂ) ⊗ₜ[ℚ] v i)) =
        (1 : ℂ) ⊗ₜ[ℚ] exteriorPower.ιMulti ℚ n v := by
    apply (ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ (A.variety.rationalCohomology 1) n).symm_apply_eq.mpr
    have hbase := ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChange_tmul_ιMulti ℂ (A.variety.rationalCohomology 1) n 1 v
    simpa only [one_smul, ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv_apply] using hbase.symm
  change complexExteriorCupEquiv A n
    ((ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ (A.variety.rationalCohomology 1) n).symm _) = _
  rw [he, complexExteriorCupEquiv_apply, LinearMap.baseChange_tmul, CupMap.Constructions.ExteriorCohomology.exteriorCup_wedge,
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]

/-- The complex exterior comparison retains the literal iterated cup normalization on every wedge. -/
theorem complexH1ExteriorCup_wedge (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (v : Fin n → ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :
    complexH1ExteriorCupEquiv A n (exteriorPower.ιMulti ℂ n v) =
      Constructions.complexH1CupMultilinear A n (fun i => A.h1ScalarExtension (v i)) := by
  let : Module.Finite ℚ (A.variety.rationalCohomology 1) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety 1
  let b := Module.finBasis ℚ (A.variety.rationalCohomology 1)
  let L := (complexH1ExteriorCupEquiv A n).toLinearMap.compMultilinearMap
    (exteriorPower.ιMulti ℂ n).toMultilinearMap
  let R := (Constructions.complexH1CupMultilinear A n).compLinearMap (fun _ => A.h1ScalarExtension)
  have he : L = R := by
    apply Module.Basis.ext_multilinear (fun _ : Fin n => b.baseChange ℂ)
    intro w
    change complexH1ExteriorCupEquiv A n
      (exteriorPower.ιMulti ℂ n (fun i => (b.baseChange ℂ) (w i))) =
      Constructions.complexH1CupMultilinear A n (fun i => A.h1ScalarExtension ((b.baseChange ℂ) (w i)))
    simp only [Module.Basis.baseChange_apply, ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1ScalarExtension_tmul, one_smul]
    exact (complexH1ExteriorCup_rational_wedge A n (fun i => b (w i))).trans
      (complexH1Cup_of_rational A n (fun i => b (w i))).symm
  exact congrArg (fun f : MultilinearMap ℂ
    (fun _ : Fin n => ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1))
    (A.variety.complexCohomology n) => f v) he

end

end OAI.AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup.Constructions
