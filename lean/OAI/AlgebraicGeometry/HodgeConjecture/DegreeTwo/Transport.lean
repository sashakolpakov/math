import OAI.AlgebraicGeometry.ComplexMultiplication.KnownAlgebraicity
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions

noncomputable section

section

/-!
# DegreeTwo: conditional proof development

This file does not import the admitted statement specifications. ConstructionInput and
HodgeComparisonInput below reproduce the committed prerequisite propositions, with the
identity-point scope made explicit. DegreeTwo completes the degree-two
clause from the full reviewed ChernClass input and the proved Chern/geometric
comparison. Statements/DegreeTwo exposes all three conditional conclusions.
-/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open scoped _root_.Manifold TensorProduct _root_.CategoryTheory.MonObj

open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left :=
  A.variety.property

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.Smooth A.toOver.hom :=
  A.variety.presentation.smooth

/-- The native tangent model used in the committed HolomorphicAlgebraicity statement. -/
abbrev AbelianModel (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :=
  Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ

/-- HolomorphicAlgebraicity with its required differentiability import, as an explicit input. -/
def HolomorphicAlgebraicityInput : Prop :=
  ∀ (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver →* ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver),
    MDifferentiable (𝓘(ℂ, AbelianModel A)) (𝓘(ℂ, AbelianModel B)) (fun x => f x) →
      ∃ g : A.toOver ⟶ B.toOver,
        IsMonHom g ∧ ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x

/-- The pointed universal property from HodgeComparison. -/
def IsAlbaneseMap (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) : Prop :=
  x₀ ≫ a = η[A.toOver] ∧
  ∀ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ B.toOver),
    x₀ ≫ f = η[B.toOver] →
      ∃! g : A.toOver ⟶ B.toOver, IsMonHom g ∧ a ≫ g = f

/-- The canonical Hodge-piece comparison from HodgeComparison. -/
def IsCanonicalH1 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1)) : Prop :=
  H.holomorphic = (V.pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1) ∧
  H.antiholomorphic = (V.pureBettiSubspace 0 1).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1)

/-- Construction, assumed only as an explicit theorem parameter. -/
def ConstructionInput : Prop :=
  ∀ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [ConnectedSpace X.carrier]
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver),
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
      x₀ ≫ a = 1 ∧
      ∀ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ B.toOver),
        x₀ ≫ f = 1 →
          ∃! g : A.toOver ⟶ B.toOver, IsMonHom g ∧ a ≫ g = f

/-- HodgeComparison, assumed only as an explicit theorem parameter. -/
def HodgeComparisonInput : Prop :=
  ∀ (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
    IsAlbaneseMap X x₀ A a →
    ∃ (HA : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
      (HX : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
      (e : A.variety.rationalCohomology 1 ≃ₗ[ℚ] X.rationalCohomology 1),
      IsCanonicalH1 A.variety HA ∧ IsCanonicalH1 X HX ∧
      e.toLinearMap = (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom ∧
      ComplexMultiplication.WeightOne.CM.IsHodgeMap HA HX e.toLinearMap ∧
      ComplexMultiplication.WeightOne.CM.IsHodgeMap HX HA e.symm.toLinearMap

/-- Actual scalar extension commutes with every continuous pullback. -/
theorem complexification_pullback {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y n)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification X n
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f n).hom.baseChange ℂ x) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification Y n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z c =>
      simp only [LinearMap.baseChange_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
      exact (congrArg (fun y : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n => z • y)
        (ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology_naturality f n) c)).trans
          ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n).hom.map_smul z _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- HodgeComparison's finite rational Hodge structure supplies the canonical coefficient
equivalence; no chosen or postulated Betti comparison is needed. -/
def h1ComplexificationEquiv (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1)) :
    ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology 1) ≃ₗ[ℂ] V.complexCohomology 1 := by
  letI : FiniteDimensional ℚ (V.rationalCohomology 1) := H.finiteDimensional
  exact ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (Betti.Scheme.schemePointSpace V.toOver) 1

/-- Scalar extension transports a rational pullback isomorphism to the actual
complex singular-cohomology map. -/
def complexPullbackEquiv {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (HV : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1))
    (HW : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (W.rationalCohomology 1))
    (e : W.rationalCohomology 1 ≃ₗ[ℚ] V.rationalCohomology 1) :
    W.complexCohomology 1 ≃ₗ[ℂ] V.complexCohomology 1 :=
  (h1ComplexificationEquiv W HW).symm.trans
    ((LinearEquiv.baseChange ℚ ℂ _ _ e).trans (h1ComplexificationEquiv V HV))

theorem complexPullbackEquiv_toLinearMap {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (HV : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1))
    (HW : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (W.rationalCohomology 1))
    (a : V.toOver ⟶ W.toOver)
    (e : W.rationalCohomology 1 ≃ₗ[ℚ] V.rationalCohomology 1)
    (he : e.toLinearMap = (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom) :
    (complexPullbackEquiv HV HW e).toLinearMap =
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 a).hom := by
  ext y
  obtain ⟨x, rfl⟩ := (h1ComplexificationEquiv W HW).surjective y
  change h1ComplexificationEquiv V HV
      ((LinearEquiv.baseChange ℚ ℂ _ _ e) ((h1ComplexificationEquiv W HW).symm
        (h1ComplexificationEquiv W HW x))) = _
  rw [LinearEquiv.symm_apply_apply]
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1
      (e.toLinearMap.baseChange ℂ x) = _
  rw [he]
  exact complexification_pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map a) 1 x

/-- An equivalence maps a subspace onto another if it and its inverse
preserve the respective subspaces. -/
theorem map_submodule_of_equiv {U V : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (e : U ≃ₗ[ℂ] V) (P : Submodule ℂ U) (Q : Submodule ℂ V)
    (hf : ∀ x ∈ P, e x ∈ Q) (hb : ∀ y ∈ Q, e.symm y ∈ P) :
    P.map e.toLinearMap = Q := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hf x hx
  · intro hy
    exact ⟨e.symm y, hb y hy, e.apply_symm_apply y⟩

/-- Canonical coefficient extension turns an isomorphism preserving both
rational Hodge pieces into an isomorphism of the actual complex pieces. -/
theorem complexPullbackEquiv_map_piece {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (HV : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1))
    (HW : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (W.rationalCohomology 1))
    (e : W.rationalCohomology 1 ≃ₗ[ℚ] V.rationalCohomology 1)
    (PW : Submodule ℂ (W.complexCohomology 1))
    (PV : Submodule ℂ (V.complexCohomology 1))
    (SW : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification (W.rationalCohomology 1)))
    (SV : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology 1)))
    (hW : SW = PW.comap (h1ComplexificationEquiv W HW).toLinearMap)
    (hV : SV = PV.comap (h1ComplexificationEquiv V HV).toLinearMap)
    (hf : ∀ x ∈ SW, e.toLinearMap.baseChange ℂ x ∈ SV)
    (hb : ∀ y ∈ SV, e.symm.toLinearMap.baseChange ℂ y ∈ SW) :
    PW.map (complexPullbackEquiv HV HW e).toLinearMap = PV := by
  let eB := LinearEquiv.baseChange ℚ ℂ _ _ e
  have hb' : ∀ y ∈ SV, eB.symm y ∈ SW := by
    intro y hy
    change (LinearEquiv.baseChange ℚ ℂ _ _ e).symm y ∈ SW
    rw [← LinearEquiv.baseChange_symm]
    exact hb y hy
  have heB : SW.map eB.toLinearMap = SV :=
    map_submodule_of_equiv eB SW SV hf hb'
  have hcomp : (complexPullbackEquiv HV HW e).toLinearMap.comp
      (h1ComplexificationEquiv W HW).toLinearMap =
      (h1ComplexificationEquiv V HV).toLinearMap.comp eB.toLinearMap := by
    ext x
    simp only [complexPullbackEquiv, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  have hSW : SW.map (h1ComplexificationEquiv W HW).toLinearMap = PW := by
    rw [hW]
    exact Submodule.map_comap_eq_of_surjective (h1ComplexificationEquiv W HW).surjective PW
  have hSV : SV.map (h1ComplexificationEquiv V HV).toLinearMap = PV := by
    rw [hV]
    exact Submodule.map_comap_eq_of_surjective (h1ComplexificationEquiv V HV).surjective PV
  rw [← hSW, ← Submodule.map_comp, hcomp, Submodule.map_comp, heB, hSV]

/-- The full Albanese clause of the committed DegreeTwo statement, conditional
only on its Construction and HodgeComparison inputs. -/
theorem albanese_h1_identification
    (hConstruction : ConstructionInput) (hHodgeComparison : HodgeComparisonInput)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) :
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
      (a : X.toOver ⟶ A.toOver)
      (eQ : A.variety.rationalCohomology 1 ≃ₗ[ℚ] X.rationalCohomology 1)
      (eC : A.variety.complexCohomology 1 ≃ₗ[ℂ] X.complexCohomology 1),
      x₀ ≫ a = η[A.toOver] ∧
      (∀ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ B.toOver),
        x₀ ≫ f = η[B.toOver] →
          ∃! g : A.toOver ⟶ B.toOver, IsMonHom g ∧ a ≫ g = f) ∧
      eQ.toLinearMap = (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom ∧
      eC.toLinearMap = (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 a).hom ∧
      (A.variety.pureBettiSubspace 1 0).map eC.toLinearMap = X.pureBettiSubspace 1 0 ∧
      (A.variety.pureBettiSubspace 0 1).map eC.toLinearMap = X.pureBettiSubspace 0 1 := by
  obtain ⟨A, a, ha₀, haU⟩ := hConstruction X.presentation x₀
  have ha : IsAlbaneseMap X x₀ A a := by
    simpa only [IsAlbaneseMap, MonObj.one_eq_one] using And.intro ha₀ haU
  obtain ⟨HA, HX, e, hA, hX, he, hh, hi⟩ := hHodgeComparison X x₀ A a ha
  refine ⟨A, a, e, complexPullbackEquiv HX HA e, ha.1, ha.2, he,
    complexPullbackEquiv_toLinearMap HX HA a e he, ?_, ?_⟩
  · exact complexPullbackEquiv_map_piece HX HA e _ _ _ _ hA.1 hX.1 hh hi
  · exact complexPullbackEquiv_map_piece HX HA e _ _ _ _ hA.2 hX.2
      (fun _ hx => hh.map_antiholomorphic hx)
      (fun _ hx => hi.map_antiholomorphic hx)

/-- HolomorphicAlgebraicity's analytic conclusion identifies the entire genuine cohomology
pullback, since cohomology is functorial on the underlying continuous map. -/
theorem algebraic_pullback_eq_analytic {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver →* ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (hf : Continuous (fun x => f x))
    (g : B.toOver ⟶ A.toOver)
    (hg : ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = f x) :
    ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ⟨fun x => f x, hf⟩) 1).hom := by
  have hmap : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map g =
      TopCat.ofHom ⟨fun x => f x, hf⟩ := by
    ext x
    exact hg x
  change (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map g) 1).hom = _
  rw [hmap]
  rfl

/-- Conditional HolomorphicAlgebraicity realizes a holomorphic group map algebraically and
identifies its actual rational singular-cohomology pullback. -/
theorem holomorphic_h1_algebraicity (hHolomorphicAlgebraicity : HolomorphicAlgebraicityInput)
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver →* ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (hf : MDifferentiable (𝓘(ℂ, AbelianModel B)) (𝓘(ℂ, AbelianModel A))
      (fun x => f x)) :
    ∃ g : B.toOver ⟶ A.toOver,
      IsMonHom g ∧ ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g =
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨fun x => f x, hf.continuous⟩) 1).hom := by
  obtain ⟨g, hg, hpoints⟩ := hHolomorphicAlgebraicity B A f hf
  exact ⟨g, hg, algebraic_pullback_eq_analytic f hf.continuous g hpoints⟩

/-- The universal coefficient pairing detects equality with the actual
pullback. This criterion is used when passing from lattice maps to H¹. -/
theorem pullback_eq_iff_pairing {X Y : TopCat.{0}} (f : X ⟶ Y)
    (u : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y 1 →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 1) :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 1).hom = u ↔
      ∀ c z, AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X 1 (u c) z =
        AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) Y 1 c
          (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1 z) := by
  constructor
  · rintro rfl c z
    exact AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ) f 1 c z
  · intro h
    ext c
    apply (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X 1).injective
    ext z
    exact (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ) f 1 c z).trans
      (h c z).symm

/-- A homology identification induces its canonical cohomological dual.
The homology map remains explicit; no arbitrary H¹ comparison is inserted. -/
def cohomologyFromHomologyEquiv (X : TopCat.{0})
    (L : Type) [AddCommGroup L] [Module ℚ L]
    (period : L ≃ₗ[ℚ] (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology 1) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 1 ≃ₗ[ℚ] Module.Dual ℚ L :=
  (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X 1).trans period.dualMap

/-- Naturality of the lattice-dual comparison is a proved consequence of
the actual singular homology pushforward, not a separate cohomology axiom. -/
theorem cohomologyFromHomologyEquiv_pullback
    {X Y : TopCat.{0}} (f : X ⟶ Y)
    (LX LY : Type) [AddCommGroup LX] [Module ℚ LX]
    [AddCommGroup LY] [Module ℚ LY]
    (eX : LX ≃ₗ[ℚ] (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology 1)
    (eY : LY ≃ₗ[ℚ] (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).homology 1)
    (fQ : LX →ₗ[ℚ] LY)
    (hperiod : ∀ l, eY (fQ l) = AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1 (eX l))
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y 1) :
    cohomologyFromHomologyEquiv X LX eX
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 1 c) =
      (cohomologyFromHomologyEquiv Y LY eY c).comp fQ := by
  ext l
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X 1
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 1 c) (eX l) =
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) Y 1 c (eY (fQ l))
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality, hperiod]

end

/-! Transport of the actual rational weight-one Hodge structure by an equivalence. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open scoped TensorProduct _root_.CategoryTheory.MonObj

/-- The explicit Construction and HodgeComparison inputs provide the canonical H¹ structure. -/
theorem exists_canonicalH1 (hConstruction : ConstructionInput) (hHodgeComparison : HodgeComparisonInput)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) :
    ∃ H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1), IsCanonicalH1 X H := by
  obtain ⟨A, a, ha₀, haU⟩ := hConstruction X.presentation x₀
  have ha : IsAlbaneseMap X x₀ A a := by
    simpa only [IsAlbaneseMap, MonObj.one_eq_one] using And.intro ha₀ haU
  obtain ⟨_, H, _, _, hH, _⟩ := hHodgeComparison X x₀ A a ha
  exact ⟨H, hH⟩

variable {U V : Type} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]

/-- Pull a genuine Hodge decomposition back through a rational equivalence. -/
def hodgeAlongEquiv (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (e : V ≃ₗ[ℚ] U) :
    ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V := by
  let eC := LinearEquiv.baseChange ℚ ℂ _ _ e
  let : FiniteDimensional ℚ U := H.finiteDimensional
  let : FiniteDimensional ℚ V := FiniteDimensional.of_injective e.toLinearMap e.injective
  refine ⟨H.holomorphic.comap eC.toLinearMap, H.antiholomorphic.comap eC.toLinearMap, ?_, ?_⟩
  · exact (Submodule.orderIsoMapComap eC).symm.isCompl H.complementary
  · intro x
    change e.toLinearMap.baseChange ℂ (ComplexMultiplication.WeightOne.CM.coefficientConjugation V x) ∈ H.antiholomorphic ↔
      e.toLinearMap.baseChange ℂ x ∈ H.holomorphic
    rw [ComplexMultiplication.WeightOne.CM.baseChange_coefficientConjugation]
    exact H.conjugate_mem _

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions
