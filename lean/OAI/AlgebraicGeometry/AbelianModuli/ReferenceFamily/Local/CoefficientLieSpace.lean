import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AlgebraLiftCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.InfinitesimalAction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.RelativeLifts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ConormalRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.TangentBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PointCoefficients
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

/-! # Coefficient Lie Space -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieSpace.LocalCoefficientLie

noncomputable section

/-! Relative infinitesimal points at a local-ring-valued section, with
the original affine coefficient maps. The coefficient ring may have
nilpotents; its actual dual-number ring supplies the infinitesimal test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable (C : Type) [CommRing C]

def dualBase : Spec (.of (DualNumber C)) ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (algebraMap C (DualNumber C)))

instance dualNumber_isLocalRing [IsLocalRing C] : IsLocalRing (DualNumber C) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro x
  simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.fst_one] using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

variable {C} [IsLocalRing C] {X Y : Scheme.{0}} (p : Y ⟶ X) (s : X ⟶ Y)
  (q : Spec (.of C) ⟶ X)

def zeroPoint : Spec (.of (DualNumber C)) ⟶ Y := (dualBase C ≫ q) ≫ s

def Space := PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.Space (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
  (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) p (zeroPoint s q)

instance : AddCommGroup (Space p s q) :=
  inferInstanceAs (AddCommGroup (PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.Space (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
    (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) p (zeroPoint s q)))

instance : Module (DualNumber C) (Space p s q) :=
  inferInstanceAs (Module (DualNumber C) (PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.Space (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
    (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) p (zeroPoint s q)))

instance : Module C (Space p s q) := Module.compHom (Space p s q) (algebraMap C (DualNumber C))

instance : IsScalarTower C (DualNumber C) (Space p s q) :=
  by
  constructor
  intro a b v
  change (a • b) • v = (algebraMap C (DualNumber C) a) • (b • v)
  have h : (a • b : DualNumber C) = algebraMap C (DualNumber C) a * b := by
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [h, mul_smul]

abbrev baseCoefficientAlgebra : Algebra Γ(X, ⊤) C := (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q).toAlgebra

abbrev ambientCoefficientAlgebra : Algebra Γ(Y, ⊤) C :=
  ((HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q).comp s.appTop.hom).toAlgebra

omit [IsLocalRing C] in
theorem coefficientScalarTower (hs : s ≫ p = 𝟙 X) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := baseCoefficientAlgebra q
    letI := ambientCoefficientAlgebra s q
    IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) C := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := baseCoefficientAlgebra q
  let := ambientCoefficientAlgebra s q
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (congrArg (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q)
    (ConcreteCategory.congr_hom (Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.section_appTop p s hs) r)).symm

theorem zeroPoint_coefficients :
    PELModuli.IntegralModel.Affine.StalkLifts.AffineStalkLifts.globalMap (Scheme.stalkClosedPointTo (zeroPoint s q)) =
      (algebraMap C (DualNumber C)).comp
        ((HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q).comp s.appTop.hom) := by
  refine (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap_stalk (zeroPoint s q)).symm.trans ?_
  apply RingHom.ext
  intro b
  change (Scheme.ΓSpecIso (.of (DualNumber C))).hom ((zeroPoint s q).appTop b) =
    algebraMap C (DualNumber C) ((Scheme.ΓSpecIso (.of C)).hom (q.appTop (s.appTop b)))
  rw [zeroPoint, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap C (DualNumber C))))
    (q.appTop (s.appTop b))

theorem reference_eq :
    letI := ambientCoefficientAlgebra s q
    PELModuli.IntegralModel.Affine.StalkLifts.AffineStalkLifts.globalMap (Scheme.stalkClosedPointTo (zeroPoint s q)) =
      algebraMap Γ(Y, ⊤) (DualNumber C) := by
  let := ambientCoefficientAlgebra s q
  exact zeroPoint_coefficients s q

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieSpace.LocalCoefficientLie
