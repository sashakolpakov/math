import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSliceLocalAction
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductPurity
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeUniversalCoefficientNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalDerivative

/-! # Rational Normal Slice Action -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RationalNormalSliceAction.Cycles

noncomputable section

/-!
# Rational dual normal classes and nonlinear normal-coordinate pullback

The normalized rational class is characterized by actual evaluation on the
rationalized integral generator. Naturality of the proved relative universal
coefficient equivalence transfers preservation of that integral generator
to exact pullback equality of the rational class.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Topology _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section IntegralNormalization

variable (X : TopCat.{0}) (A : Set X) (n : ℕ)

/-- Rationalize a specified genuine integral relative-homology normalization. -/
def rationalRelativeNormalizationIso
    (e : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ) :
    RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A n ≅ ModuleCat.of ℚ ℚ :=
  RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n ≪≫ RationalScalarExtension.Cycles.rationalizeModules.mapIso e ≪≫ RationalScalarExtension.Cycles.rationalizeUnitIso

/-- The actual rational cohomology class whose evaluation is the rationalized
integral coordinate map. -/
def relativeRationalDualOfIntegralIso
    (e : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n :=
  (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n).symm
    (rationalRelativeNormalizationIso X A n e).hom.hom

@[simp]
theorem relativeRationalDualOfIntegralIso_functional
    (e : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n (relativeRationalDualOfIntegralIso X A n e) =
      (rationalRelativeNormalizationIso X A n e).hom.hom :=
  (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n).apply_symm_apply _

/-- This class evaluates to one on the actual rationalized generator. -/
theorem relativeRationalDualOfIntegralIso_evaluation
    (e : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n (relativeRationalDualOfIntegralIso X A n e)
      ((rationalRelativeNormalizationIso X A n e).inv 1) = 1 := by
  rw [relativeRationalDualOfIntegralIso_functional]
  change ((rationalRelativeNormalizationIso X A n e).inv ≫
    (rationalRelativeNormalizationIso X A n e).hom) 1 = 1
  rw [Iso.inv_hom_id]
  rfl

/-- Evaluation one on that generator uniquely determines the rational dual class. -/
theorem relativeRationalDualOfIntegralIso_unique
    (e : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n)
    (ha : RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n a
      ((rationalRelativeNormalizationIso X A n e).inv 1) = 1) :
    a = relativeRationalDualOfIntegralIso X A n e := by
  apply (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n).injective
  rw [relativeRationalDualOfIntegralIso_functional]
  exact (DualNormalization.Cycles.dual_normalization_eq_one_iff
    (rationalRelativeNormalizationIso X A n e).toLinearEquiv
    (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n a)).mp ha

end IntegralNormalization

section Naturality

variable {X Y : TopCat.{0}} {A : Set X} {B : Set Y}

/-- Preservation of the generating integral class determines the whole
integral coordinate map, since maps out of `ℤ` are determined by one. -/
theorem relativeIntegralNormalization_naturality (f : X ⟶ Y) (hf : Set.MapsTo f A B)
    (n : ℕ) (eX : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ)
    (eY : LocalHomology.Cycles.relativeSingularHomology Y B n ≅ ModuleCat.of ℤ ℤ)
    (hgen : LocalHomology.Cycles.relativeSingularHomologyMap f hf n (eX.inv 1) = eY.inv 1) :
    LocalHomology.Cycles.relativeSingularHomologyMap f hf n ≫ eY.hom = eX.hom := by
  apply (cancel_epi eX.inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change eY.hom (LocalHomology.Cycles.relativeSingularHomologyMap f hf n (eX.inv 1)) = eX.hom (eX.inv 1)
  rw [hgen]
  change (eY.inv ≫ eY.hom) 1 = (eX.inv ≫ eX.hom) 1
  rw [Iso.inv_hom_id, Iso.inv_hom_id]

/-- Rationalization of the actual integral normalizations respects a genuine
map of pairs whose integral coordinate maps commute. -/
theorem rationalRelativeNormalizationIso_naturality
    (f : X ⟶ Y) (hf : Set.MapsTo f A B) (n : ℕ)
    (eX : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ)
    (eY : LocalHomology.Cycles.relativeSingularHomology Y B n ≅ ModuleCat.of ℤ ℤ)
    (he : LocalHomology.Cycles.relativeSingularHomologyMap f hf n ≫ eY.hom = eX.hom) :
    HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hf) n ≫
        (rationalRelativeNormalizationIso Y B n eY).hom =
      (rationalRelativeNormalizationIso X A n eX).hom := by
  calc
    _ = (HomologicalComplex.homologyMap (RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hf) n ≫
        (RationalRelativeHomology.Cycles.rationalRelativeHomologyIso Y B n).hom) ≫
          RationalScalarExtension.Cycles.rationalizeModules.map eY.hom ≫ RationalScalarExtension.Cycles.rationalizeUnitIso.hom := by
      simp only [rationalRelativeNormalizationIso, Iso.trans_hom,
        Functor.mapIso_hom, Category.assoc]
    _ = ((RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).hom ≫
        RationalScalarExtension.Cycles.rationalizeModules.map (LocalHomology.Cycles.relativeSingularHomologyMap f hf n)) ≫
          RationalScalarExtension.Cycles.rationalizeModules.map eY.hom ≫ RationalScalarExtension.Cycles.rationalizeUnitIso.hom := by
      rw [RationalRelativeHomology.Cycles.rationalRelativeHomologyIso_hom_naturality]
    _ = (RationalRelativeHomology.Cycles.rationalRelativeHomologyIso X A n).hom ≫
        RationalScalarExtension.Cycles.rationalizeModules.map (LocalHomology.Cycles.relativeSingularHomologyMap f hf n ≫ eY.hom) ≫
          RationalScalarExtension.Cycles.rationalizeUnitIso.hom := by
      rw [RationalScalarExtension.Cycles.rationalizeModules.map_comp]
      simp only [Category.assoc]
    _ = _ := by
      rw [he]
      rfl

/-- Actual relative UCT naturality transfers an integral normalization square
to exact pullback equality of the normalized rational duals. -/
theorem relativeRationalDualOfIntegralIso_pullback
    (f : X ⟶ Y) (hf : Set.MapsTo f A B) (n : ℕ)
    (eX : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ)
    (eY : LocalHomology.Cycles.relativeSingularHomology Y B n ≅ ModuleCat.of ℤ ℤ)
    (he : LocalHomology.Cycles.relativeSingularHomologyMap f hf n ≫ eY.hom = eX.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n
      (relativeRationalDualOfIntegralIso Y B n eY) = relativeRationalDualOfIntegralIso X A n eX := by
  apply (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n).injective
  rw [RelativeUniversalCoefficientNaturality.Cycles.relativeUniversalCoefficientEquiv_naturality,
    relativeRationalDualOfIntegralIso_functional, relativeRationalDualOfIntegralIso_functional]
  exact congrArg ModuleCat.Hom.hom (rationalRelativeNormalizationIso_naturality f hf n eX eY he)

/-- Preservation of the actual integral generator forces preservation of its
normalized rational dual under the actual cohomological pullback. -/
theorem relativeRationalDualOfIntegralIso_pullback_of_generator
    (f : X ⟶ Y) (hf : Set.MapsTo f A B) (n : ℕ)
    (eX : LocalHomology.Cycles.relativeSingularHomology X A n ≅ ModuleCat.of ℤ ℤ)
    (eY : LocalHomology.Cycles.relativeSingularHomology Y B n ≅ ModuleCat.of ℤ ℤ)
    (hgen : LocalHomology.Cycles.relativeSingularHomologyMap f hf n (eX.inv 1) = eY.inv 1) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n
      (relativeRationalDualOfIntegralIso Y B n eY) = relativeRationalDualOfIntegralIso X A n eX :=
  relativeRationalDualOfIntegralIso_pullback f hf n eX eY
    (relativeIntegralNormalization_naturality f hf n eX eY hgen)

end Naturality

/-- The existing punctured-normal rational class has exactly the dual
normalization obtained from the specified integral local generator. -/
theorem complexNormalRationalDualClass_eq_integralDual (p : ℕ) :
    RationalLocalPurity.Cycles.complexNormalRationalDualClass p = relativeRationalDualOfIntegralIso
      (TopCat.of (Fin p → ℂ)) ({0}ᶜ : Set (Fin p → ℂ)) (2 * p)
        (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p) := by
  apply (RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ _ _ _).injective
  rw [RationalLocalPurity.Cycles.complexNormalRationalDualClass_functional, relativeRationalDualOfIntegralIso_functional]
  rfl

section ProductNormalization

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The already defined product Thom class agrees with the rational dual of
the actual integral product normalization, by projection naturality. -/
theorem complexNormalProductRationalClass_eq_integralDual (p : ℕ) :
    NormalProductPurity.Cycles.complexNormalProductRationalClass E p = relativeRationalDualOfIntegralIso
      (TopCat.of (E × (Fin p → ℂ))) (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) (2 * p)
        (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E p) := by
  rw [NormalProductPurity.Cycles.complexNormalProductRationalClass_eq_pullback,
    complexNormalRationalDualClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_pullback
    (NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ)) (NormalProductPair.Cycles.normalProductProjection_mapsTo E (Fin p → ℂ) 0)
    (2 * p) (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E p) (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p) rfl

/-- Its value on the actual rationalized integral product generator is one. -/
theorem complexNormalProductRationalClass_integral_evaluation (p : ℕ) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (E × (Fin p → ℂ)))
      (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) (2 * p) (NormalProductPurity.Cycles.complexNormalProductRationalClass E p)
        ((rationalRelativeNormalizationIso (TopCat.of (E × (Fin p → ℂ)))
          (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) (2 * p)
          (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E p)).inv 1) = 1 := by
  rw [complexNormalProductRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_evaluation _ _ _ _

/-- The product rational class is uniquely characterized by this evaluation. -/
theorem complexNormalProductRationalClass_unique_integral (p : ℕ)
    (a : NormalProductPurity.Cycles.complexNormalProductRationalCohomology E p (2 * p))
    (ha : RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of (E × (Fin p → ℂ)))
      (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) (2 * p) a
        ((rationalRelativeNormalizationIso (TopCat.of (E × (Fin p → ℂ)))
          (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0) (2 * p)
          (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E p)).inv 1) = 1) :
    a = NormalProductPurity.Cycles.complexNormalProductRationalClass E p := by
  rw [complexNormalProductRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_unique _ _ _ _ a ha

end ProductNormalization

section ProductPullback

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] (p : ℕ)

/-- Preservation of the actual integral product normal class gives exact
pullback equality for the already defined rational product Thom class. -/
theorem complexNormalProductRationalClass_pullback_of_integral
    (φ : TopCat.of (E × (Fin p → ℂ)) ⟶ TopCat.of (E' × (Fin p → ℂ)))
    (hφ : Set.MapsTo φ (NormalProductPair.Cycles.normalProductComplement E (Fin p → ℂ) 0)
      (NormalProductPair.Cycles.normalProductComplement E' (Fin p → ℂ) 0))
    (hgen : LocalHomology.Cycles.relativeSingularHomologyMap φ hφ (2 * p) (NormalProductPair.Cycles.complexNormalProductClass E p) =
      NormalProductPair.Cycles.complexNormalProductClass E' p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) φ hφ (2 * p)
      (NormalProductPurity.Cycles.complexNormalProductRationalClass E' p) = NormalProductPurity.Cycles.complexNormalProductRationalClass E p := by
  rw [complexNormalProductRationalClass_eq_integralDual,
    complexNormalProductRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_pullback_of_generator φ hφ (2 * p)
    (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E p) (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E' p) hgen

end ProductPullback

section BallNormalization

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integral top relative homology of the actual product-ball pair,
normalized by normal projection, actual excision, and the fixed normal generator. -/
def complexNormalProductBallIntegralIso (p : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    LocalHomology.Cycles.relativeSingularHomology
      (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s))
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs)) (2 * p) ≅ ModuleCat.of ℤ ℤ :=
  NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs (2 * p) ≪≫
    ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p

/-- The projection used by the cohomology construction is precisely the
projection/excision map of the integral product-ball normalization. -/
theorem normalProductBallProjection_homology (F : Type) [NormedAddCommGroup F]
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomologyMap (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E F r s)
      (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection_mapsTo E F r s hs) n =
        (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E F r s hr hs n).hom := by
  change LocalHomology.Cycles.relativeSingularHomologyMap
    (NormalProductPair.Cycles.normalProductProjection (Metric.ball (0 : E) r) (Metric.ball (0 : F) s) ≫
      NormalBallRestriction.Cycles.normalBallInclusion F s) _ n =
    LocalHomology.Cycles.relativeSingularHomologyMap
      (NormalProductPair.Cycles.normalProductProjection (Metric.ball (0 : E) r) (Metric.ball (0 : F) s))
      (NormalProductPair.Cycles.normalProductProjection_mapsTo _ _ (NormalBallRestriction.Cycles.normalBallCenter F s hs)) n ≫
      LocalHomology.Cycles.relativeSingularHomologyMap (NormalBallRestriction.Cycles.normalBallInclusion F s)
        (NormalBallRestriction.Cycles.normalBallInclusion_mapsTo F s hs) n
  rw [LocalHomology.Cycles.relativeSingularHomologyMap_comp]

/-- The rational normal class of a product of balls is the actual pullback
of the normal dual class along projection into the full normal space. -/
def complexNormalProductBallRationalClass (p : ℕ) (r s : ℝ) (_hr : 0 < r) (hs : 0 < s) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s))
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs)) (2 * p) :=
  NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyMap E (Fin p → ℂ) r s hs (2 * p) (RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

/-- This is the same class defined by the actual projection cohomology isomorphism. -/
theorem complexNormalProductBallRationalClass_eq_iso (p : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    complexNormalProductBallRationalClass E p r s hr hs =
      (NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyIso E (Fin p → ℂ) r s hr hs (2 * p)).hom
        (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) := by
  rw [NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyIso_hom]
  rfl

/-- The actual projection class is dual to the integral normal class from
the product-ball excision calculation. No radial normalization is substituted. -/
theorem complexNormalProductBallRationalClass_eq_integralDual (p : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    complexNormalProductBallRationalClass E p r s hr hs =
      relativeRationalDualOfIntegralIso _ _ (2 * p)
        (complexNormalProductBallIntegralIso E p r s hr hs) := by
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E (Fin p → ℂ) r s)
    (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection_mapsTo E (Fin p → ℂ) r s hs) (2 * p)
    (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) = _
  rw [complexNormalRationalDualClass_eq_integralDual]
  apply relativeRationalDualOfIntegralIso_pullback
  change LocalHomology.Cycles.relativeSingularHomologyMap (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection E (Fin p → ℂ) r s)
      (NormalNeighborhoodRestriction.Cycles.normalProductBallProjection_mapsTo E (Fin p → ℂ) r s hs) (2 * p) ≫
      (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).hom =
    (NormalProductPair.Cycles.normalOpenProductBallsHomologyIso E (Fin p → ℂ) r s hr hs (2 * p)).hom ≫
      (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p).hom
  rw [normalProductBallProjection_homology E (Fin p → ℂ) r s hr hs (2 * p)]

/-- The ball class evaluates to one on the actual rationalized integral ball generator. -/
theorem complexNormalProductBallRationalClass_evaluation (p : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ _ _ (2 * p)
      (complexNormalProductBallRationalClass E p r s hr hs)
      ((rationalRelativeNormalizationIso _ _ (2 * p)
        (complexNormalProductBallIntegralIso E p r s hr hs)).inv 1) = 1 := by
  rw [complexNormalProductBallRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_evaluation _ _ _ _

/-- Evaluation on the genuine normal generator uniquely fixes the rational ball class. -/
theorem complexNormalProductBallRationalClass_unique (p : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s))
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs)) (2 * p))
    (ha : RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ _ _ (2 * p) a
      ((rationalRelativeNormalizationIso _ _ (2 * p)
        (complexNormalProductBallIntegralIso E p r s hr hs)).inv 1) = 1) :
    a = complexNormalProductBallRationalClass E p r s hr hs := by
  rw [complexNormalProductBallRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_unique _ _ _ _ a ha

omit [NormedSpace ℝ E] in
/-- The rational normal classes agree under actual shrinking of both coordinate balls. -/
theorem complexNormalProductBallRationalClass_restrict (p : ℕ) {r r' s s' : ℝ}
    (hr : 0 < r) (hr' : 0 < r') (hs : 0 < s) (hs' : 0 < s')
    (hrr : r' ≤ r) (hss : s' ≤ s) :
    NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyRestriction E (Fin p → ℂ) hs hs' hrr hss (2 * p)
      (complexNormalProductBallRationalClass E p r s hr hs) =
        complexNormalProductBallRationalClass E p r' s' hr' hs' :=
  ConcreteCategory.congr_hom
    (NormalNeighborhoodRestriction.Cycles.normalProductBallCohomologyMap_restrict E (Fin p → ℂ) hs hs' hrr hss (2 * p))
    (RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

end BallNormalization

section BallInclusion

variable (E F : Type) [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The actual inclusion of both coordinate balls into the full product. -/
def normalProductBallsInclusion (r s : ℝ) :
    TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s) ⟶ TopCat.of (E × F) :=
  TopCat.ofHom ⟨fun z => (z.1.val, z.2.val),
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)⟩

theorem normalProductBallsInclusion_mapsTo (r s : ℝ) (hs : 0 < s) :
    Set.MapsTo (normalProductBallsInclusion E F r s)
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
        (LocalDerivativeHomology.Cycles.ballZero F s hs)) (NormalProductPair.Cycles.normalProductComplement E F 0) := by
  intro z hz h
  exact hz (Subtype.ext h)

end BallInclusion

section ProductRestriction

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical ball class is exactly the restriction of the canonical
full-product class along the genuine inclusion of pairs. -/
theorem complexNormalProductRationalClass_restrict_balls (p : ℕ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (normalProductBallsInclusion E (Fin p → ℂ) r s)
      (normalProductBallsInclusion_mapsTo E (Fin p → ℂ) r s hs) (2 * p)
      (NormalProductPurity.Cycles.complexNormalProductRationalClass E p) =
        complexNormalProductBallRationalClass E p r s hr hs := by
  rw [NormalProductPurity.Cycles.complexNormalProductRationalClass_eq_pullback]
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (NormalProductPair.Cycles.normalProductProjection E (Fin p → ℂ))
      (NormalProductPair.Cycles.normalProductProjection_mapsTo E (Fin p → ℂ) 0) (2 * p) ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (normalProductBallsInclusion E (Fin p → ℂ) r s)
      (normalProductBallsInclusion_mapsTo E (Fin p → ℂ) r s hs) (2 * p))
        (RationalLocalPurity.Cycles.complexNormalRationalDualClass p) = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

end ProductRestriction

section BallPullback

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] (p : ℕ)

/-- Integral generator preservation for an actual ball-to-product pair map
implies exact rational Thom-class pullback equality. -/
theorem complexNormalProductBallRationalClass_pullback_of_integral
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (φ : TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s) ⟶
      TopCat.of (E' × (Fin p → ℂ)))
    (hφ : Set.MapsTo φ
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs)) (NormalProductPair.Cycles.normalProductComplement E' (Fin p → ℂ) 0))
    (hgen : LocalHomology.Cycles.relativeSingularHomologyMap φ hφ (2 * p)
      (NormalSliceLocalAction.Cycles.complexNormalOpenProductBallsClass E p r s hr hs) = NormalProductPair.Cycles.complexNormalProductClass E' p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) φ hφ (2 * p)
      (NormalProductPurity.Cycles.complexNormalProductRationalClass E' p) =
        complexNormalProductBallRationalClass E p r s hr hs := by
  rw [complexNormalProductRationalClass_eq_integralDual,
    complexNormalProductBallRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_pullback_of_generator φ hφ (2 * p)
    (complexNormalProductBallIntegralIso E p r s hr hs) (NormalProductPair.Cycles.complexNormalProductTopHomologyIso E' p) hgen

/-- The same exact duality statement applies between two genuine product-ball pairs. -/
theorem complexNormalProductBallRationalClass_pullback_between_balls
    (r s r' s' : ℝ) (hr : 0 < r) (hs : 0 < s) (hr' : 0 < r') (hs' : 0 < s')
    (φ : TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : Fin p → ℂ) s) ⟶
      TopCat.of (Metric.ball (0 : E') r' × Metric.ball (0 : Fin p → ℂ) s'))
    (hφ : Set.MapsTo φ
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : Fin p → ℂ) s)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s hs))
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E') r') (Metric.ball (0 : Fin p → ℂ) s')
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) s' hs')))
    (hgen : LocalHomology.Cycles.relativeSingularHomologyMap φ hφ (2 * p)
      (NormalSliceLocalAction.Cycles.complexNormalOpenProductBallsClass E p r s hr hs) =
        NormalSliceLocalAction.Cycles.complexNormalOpenProductBallsClass E' p r' s' hr' hs') :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) φ hφ (2 * p)
      (complexNormalProductBallRationalClass E' p r' s' hr' hs') =
        complexNormalProductBallRationalClass E p r s hr hs := by
  rw [complexNormalProductBallRationalClass_eq_integralDual,
    complexNormalProductBallRationalClass_eq_integralDual]
  exact relativeRationalDualOfIntegralIso_pullback_of_generator φ hφ (2 * p)
    (complexNormalProductBallIntegralIso E p r s hr hs)
    (complexNormalProductBallIntegralIso E' p r' s' hr' hs') hgen

end BallPullback

section NonlinearPullback

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] {p : ℕ}

/-- The actual integral normal-slice invariance theorem implies exact
pullback equality of the normalized rational Thom classes after shrinking. -/
theorem exists_normalSlice_rationalClass_pullback
    (Φ : E × (Fin p → ℂ) → E' × (Fin p → ℂ))
    (W : Set (E × (Fin p → ℂ))) (hW : W ∈ 𝓝 (0, 0)) (hΦ : ContinuousOn Φ W)
    (hpair : ∀ x ∈ W, x.2 ≠ 0 → (Φ x).2 ≠ 0) (hzero : (Φ (0, 0)).2 = 0)
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hderiv : HasFDerivAt (fun y => (Φ (0, y)).2)
      ((L.restrictScalars ℝ) : _ →L[ℝ] _) 0) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W),
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalSliceLocalAction.Cycles.normalProductBallMap Φ r s (hΦ.mono hsub))
        (NormalSliceLocalAction.Cycles.normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
          (fun x hx => hpair x (hsub hx))) (2 * p)
        (NormalProductPurity.Cycles.complexNormalProductRationalClass E' p) =
          complexNormalProductBallRationalClass E p r s hr hs := by
  obtain ⟨r, s, hr, hs, hsub, hgen⟩ :=
    NormalSliceLocalAction.Cycles.exists_normalProductBallMap_class_invariant Φ W hW hΦ hpair hzero L hderiv
  exact ⟨r, s, hr, hs, hsub,
    complexNormalProductBallRationalClass_pullback_of_integral p r s hr hs
      (NormalSliceLocalAction.Cycles.normalProductBallMap Φ r s (hΦ.mono hsub))
      (NormalSliceLocalAction.Cycles.normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
        (fun x hx => hpair x (hsub hx))) hgen⟩

end NonlinearPullback

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] {p : ℕ}

/-- Rational normal-class pullback for a genuine local coordinate map with
its actual complex ambient derivative and proved normal-block invertibility. -/
theorem exists_normalCoordinate_rationalClass_pullback
    (Φ : E × (Fin p → ℂ) → E × (Fin p → ℂ))
    (W : Set (E × (Fin p → ℂ))) (hW : W ∈ 𝓝 (0, 0)) (hΦ : ContinuousOn Φ W)
    (hpair : ∀ x ∈ W, x.2 ≠ 0 → (Φ x).2 ≠ 0) (hzero : (Φ (0, 0)).2 = 0)
    (L : (E × (Fin p → ℂ)) ≃L[ℂ] (E × (Fin p → ℂ)))
    (hL : ∀ x : E, (L (x, 0)).2 = 0) (hLi : ∀ x : E, (L.symm (x, 0)).2 = 0)
    (hderiv : HasFDerivAt Φ L.toContinuousLinearMap (0, 0)) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ W),
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalSliceLocalAction.Cycles.normalProductBallMap Φ r s (hΦ.mono hsub))
        (NormalSliceLocalAction.Cycles.normalProductBallMap_mapsTo Φ r s hs (hΦ.mono hsub) 0
          (fun x hx => hpair x (hsub hx))) (2 * p)
        (NormalProductPurity.Cycles.complexNormalProductRationalClass E p) =
          complexNormalProductBallRationalClass E p r s hr hs :=
  exists_normalSlice_rationalClass_pullback Φ W hW hΦ hpair hzero
    (ComplexNormalBlock.Cycles.normalBlock L hL hLi) (NormalSliceLocalAction.Cycles.normalSlice_hasFDerivAt_normalBlock Φ L hL hLi hderiv)

/-- A genuine complex local diffeomorphism preserving the normal zero locus
has the required rational pullback property. Invertibility and both horizontal
derivative conditions are derived from the map and its actual inverse. -/
theorem exists_normalDiffeomorph_rationalClass_pullback
    (e : OpenPartialHomeomorph (E × (Fin p → ℂ)) (E × (Fin p → ℂ)))
    (he : e.MDifferentiable 𝓘(ℂ, E × (Fin p → ℂ)) 𝓘(ℂ, E × (Fin p → ℂ)))
    (h0 : (0, 0) ∈ e.source) (he0 : e (0, 0) = (0, 0))
    (hpres : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) :
    ∃ (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
      (hsub : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : Fin p → ℂ) s ⊆ e.source),
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (NormalSliceLocalAction.Cycles.normalProductBallMap e r s (e.continuousOn.mono hsub))
        (NormalSliceLocalAction.Cycles.normalProductBallMap_mapsTo e r s hs (e.continuousOn.mono hsub) 0
          (fun x hx hz h => hz ((hpres x (hsub hx)).mp h))) (2 * p)
        (NormalProductPurity.Cycles.complexNormalProductRationalClass E p) =
          complexNormalProductBallRationalClass E p r s hr hs := by
  let L := NormalDerivative.Cycles.normalDiffeomorphDerivative e he h0
  have hd := NormalDerivative.Cycles.normalDiffeomorphDerivative_hasFDerivAt e he h0
  obtain ⟨hL, hLi⟩ := NormalDerivative.Cycles.normalCoordinateDerivative_horizontal_pair e L h0 he0 hd hpres
  exact exists_normalCoordinate_rationalClass_pullback e e.source
    (e.open_source.mem_nhds h0) e.continuousOn
    (fun x hx hz h => hz ((hpres x hx).mp h))
    (congrArg Prod.snd he0) L hL hLi hd

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RationalNormalSliceAction.Cycles
