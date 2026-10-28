import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.DualPointCoefficients
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualLifts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ConormalRestriction
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

/-! # Section Lie -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.SectionLie

noncomputable section

section

/-! The actual relative infinitesimal points at a field-valued
smooth section, with their canonical coefficient algebras. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AffineSectionLie
open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {X Y : Scheme.{0}} (p : Y ⟶ X) (s : X ⟶ Y)
  {k : Type} [Field k] (q : Spec (.of k) ⟶ X)

def zeroPoint : Spec (.of (DualNumber k)) ⟶ Y := DualNumberReduction.AlgebraicLie.dualBase k ≫ q ≫ s

def Space := AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
  (Scheme.stalkClosedPointTo (zeroPoint s q)) p

instance : AddCommGroup (Space p s q) :=
  inferInstanceAs (AddCommGroup (AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule (DualNumberReduction.AlgebraicLie.dualIdeal k)
    (DualNumberReduction.AlgebraicLie.dualIdeal_square k) (Scheme.stalkClosedPointTo (zeroPoint s q)) p))

instance : Module (DualNumber k) (Space p s q) :=
  inferInstanceAs (Module (DualNumber k) (AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule (DualNumberReduction.AlgebraicLie.dualIdeal k)
    (DualNumberReduction.AlgebraicLie.dualIdeal_square k) (Scheme.stalkClosedPointTo (zeroPoint s q)) p))

instance : Module k (Space p s q) := Module.compHom (Space p s q) (algebraMap k (DualNumber k))

instance : IsScalarTower k (DualNumber k) (Space p s q) := by
  constructor
  intro a b v
  change (a • b) • v = (algebraMap k (DualNumber k) a) • (b • v)
  have h : (a • b : DualNumber k) = algebraMap k (DualNumber k) a * b := by
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [h, mul_smul]

abbrev baseFieldAlgebra : Algebra Γ(X, ⊤) k := (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q).toAlgebra

abbrev ambientFieldAlgebra : Algebra Γ(Y, ⊤) k :=
  ((HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q).comp s.appTop.hom).toAlgebra

theorem fieldScalarTower (hs : s ≫ p = 𝟙 X) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := baseFieldAlgebra q
    letI := ambientFieldAlgebra s q
    IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) k := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := baseFieldAlgebra q
  let := ambientFieldAlgebra s q
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (congrArg (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q)
    (ConcreteCategory.congr_hom (Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.section_appTop p s hs) r)).symm

theorem reference_eq :
    letI := ambientFieldAlgebra s q
    StalkLifts.AffineStalkLifts.globalMap (Scheme.stalkClosedPointTo (zeroPoint s q)) =
      algebraMap Γ(Y, ⊤) (DualNumber k) := by
  let := ambientFieldAlgebra s q
  exact Section.DualPointCoefficients.section_dualPoint_coefficients s q

end AffineSectionLie

end

section

/-! Coordinate-ring lifts of actual relative infinitesimal section
points, with an explicit formula on every affine function. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AffineSectionLie
open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {X Y : Scheme.{0}} [IsAffine X] (p : Y ⟶ X) (s : X ⟶ Y)
  (hs : s ≫ p = 𝟙 X) {k : Type} [Field k] (q : Spec (.of k) ⟶ X)

def algebraLift (v : Space p s q) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := baseFieldAlgebra q
    letI := ambientFieldAlgebra s q
    letI := fieldScalarTower p s q hs
    Relative.DualLifts.RelativeDualLifts.Space Γ(X, ⊤) Γ(Y, ⊤) k := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := baseFieldAlgebra q
  let := ambientFieldAlgebra s q
  let := fieldScalarTower p s q hs
  let e := Scheme.stalkClosedPointTo (zeroPoint s q)
  refine ⟨⟨(StalkLifts.AffineStalkLifts.toGlobal (DualNumberReduction.AlgebraicLie.dualIdeal k)
    (DualNumberReduction.AlgebraicLie.dualIdeal_square k) e v.val).hom, ?_⟩, ?_⟩
  · intro b
    have h := v.val.congruent (Y.presheaf.Γgerm ((zeroPoint s q) (IsLocalRing.closedPoint (DualNumber k))) b)
    change _ - StalkLifts.AffineStalkLifts.globalMap e b ∈ DualNumberReduction.AlgebraicLie.dualIdeal k at h
    rw [reference_eq s q] at h
    exact h
  · intro r
    have h := (RelativeLifts.AffineStalkLifts.toGlobal_relative_iff p (DualNumberReduction.AlgebraicLie.dualIdeal k)
      (DualNumberReduction.AlgebraicLie.dualIdeal_square k) e v.val).mp v.property r
    exact h.trans ((RingHom.congr_fun (reference_eq s q) (p.appTop r)).trans
      (IsScalarTower.algebraMap_apply Γ(X, ⊤) Γ(Y, ⊤) (DualNumber k) r).symm)

theorem algebraLift_hom (v : Space p s q) (b : Γ(Y, ⊤)) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := baseFieldAlgebra q
    letI := ambientFieldAlgebra s q
    letI := fieldScalarTower p s q hs
    (algebraLift p s hs q v).val.hom b = v.val.hom
      (Y.presheaf.Γgerm ((zeroPoint s q) (IsLocalRing.closedPoint (DualNumber k))) b) := rfl

def toAlgebraLifts :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := baseFieldAlgebra q
    letI := ambientFieldAlgebra s q
    letI := fieldScalarTower p s q hs
    Space p s q →ₗ[DualNumber k] Relative.DualLifts.RelativeDualLifts.Space Γ(X, ⊤) Γ(Y, ⊤) k := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := baseFieldAlgebra q
  let := ambientFieldAlgebra s q
  let := fieldScalarTower p s q hs
  refine { toFun := algebraLift p s hs q, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    apply Subtype.ext
    apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
    apply RingHom.ext
    intro b
    change (v.val + w.val).hom (Y.presheaf.Γgerm _ b) =
      (algebraLift p s hs q v).val.hom b + (algebraLift p s hs q w).val.hom b -
        algebraMap Γ(Y, ⊤) (DualNumber k) b
    rw [AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.add_hom, algebraLift_hom, algebraLift_hom]
    exact congrArg (fun z => v.val.hom (Y.presheaf.Γgerm _ b) +
      w.val.hom (Y.presheaf.Γgerm _ b) - z) (RingHom.congr_fun (reference_eq s q) b)
  · intro c v
    apply Subtype.ext
    apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
    apply RingHom.ext
    intro b
    change (c • v.val).hom (Y.presheaf.Γgerm _ b) =
      algebraMap Γ(Y, ⊤) (DualNumber k) b +
        c * ((algebraLift p s hs q v).val.hom b - algebraMap Γ(Y, ⊤) (DualNumber k) b)
    rw [AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.smul_hom, algebraLift_hom]
    exact congrArg (fun z => z + c * (v.val.hom (Y.presheaf.Γgerm _ b) - z))
      (RingHom.congr_fun (reference_eq s q) b)

end AffineSectionLie

end

section

/-! The coordinate map on actual affine relative section Lie
points is bijective and coefficient-linear. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AffineSectionLie
open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
  (p : Y ⟶ X) (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X)
  {k : Type} [Field k] (q : Spec (.of k) ⟶ X)

theorem toAlgebraLifts_bijective :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := baseFieldAlgebra q
    letI := ambientFieldAlgebra s q
    letI := fieldScalarTower p s q hs
    Function.Bijective (toAlgebraLifts p s hs q) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := baseFieldAlgebra q
  let := ambientFieldAlgebra s q
  let := fieldScalarTower p s q hs
  let e := Scheme.stalkClosedPointTo (zeroPoint s q)
  constructor
  · intro v w h
    apply Subtype.ext
    apply (StalkLifts.AffineStalkLifts.toGlobal_bijective (DualNumberReduction.AlgebraicLie.dualIdeal k)
      (DualNumberReduction.AlgebraicLie.dualIdeal_square k) e).injective
    apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
    apply RingHom.ext
    intro b
    exact congrArg (fun z : Relative.DualLifts.RelativeDualLifts.Space Γ(X, ⊤) Γ(Y, ⊤) k => z.val.hom b) h
  · intro w
    let w₀ : AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
        (StalkLifts.AffineStalkLifts.globalMap e) := ⟨w.val.hom, fun b => by
          rw [reference_eq s q]
          exact w.val.congruent b⟩
    obtain ⟨v, hg⟩ := (StalkLifts.AffineStalkLifts.toGlobal_bijective (DualNumberReduction.AlgebraicLie.dualIdeal k)
      (DualNumberReduction.AlgebraicLie.dualIdeal_square k) e).surjective w₀
    have hv : v ∈ AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule (DualNumberReduction.AlgebraicLie.dualIdeal k)
        (DualNumberReduction.AlgebraicLie.dualIdeal_square k) e p := by
      apply (RelativeLifts.AffineStalkLifts.toGlobal_relative_iff p (DualNumberReduction.AlgebraicLie.dualIdeal k)
        (DualNumberReduction.AlgebraicLie.dualIdeal_square k) e v).mpr
      intro r
      have hr := congrArg (fun z : AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift (DualNumberReduction.AlgebraicLie.dualIdeal k)
        (DualNumberReduction.AlgebraicLie.dualIdeal_square k) (StalkLifts.AffineStalkLifts.globalMap e) => z.hom (p.appTop r)) hg
      exact hr.trans ((w.property r).trans
        ((IsScalarTower.algebraMap_apply Γ(X, ⊤) Γ(Y, ⊤) (DualNumber k) r).trans
          (RingHom.congr_fun (reference_eq s q) (p.appTop r)).symm))
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
    apply RingHom.ext
    intro b
    exact congrArg (fun z : AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift (DualNumberReduction.AlgebraicLie.dualIdeal k)
      (DualNumberReduction.AlgebraicLie.dualIdeal_square k) (StalkLifts.AffineStalkLifts.globalMap e) => z.hom b) hg

def algebraEquiv :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := baseFieldAlgebra q
    letI := ambientFieldAlgebra s q
    letI := fieldScalarTower p s q hs
    Space p s q ≃ₗ[k] Relative.DualLifts.RelativeDualLifts.Space Γ(X, ⊤) Γ(Y, ⊤) k := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := baseFieldAlgebra q
  let := ambientFieldAlgebra s q
  let := fieldScalarTower p s q hs
  exact (LinearEquiv.ofBijective (toAlgebraLifts p s hs q)
    (toAlgebraLifts_bijective p s hs q)).restrictScalars k

theorem algebraEquiv_hom (v : Space p s q) (b : Γ(Y, ⊤)) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := baseFieldAlgebra q
    letI := ambientFieldAlgebra s q
    letI := fieldScalarTower p s q hs
    (algebraEquiv p s hs q v).val.hom b = v.val.hom
      (Y.presheaf.Γgerm ((zeroPoint s q) (IsLocalRing.closedPoint (DualNumber k))) b) := rfl

end AffineSectionLie

end

/-! Actual infinitesimal points at every field-valued affine smooth
section are the linear dual of its actual conormal, with the germ formula. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace AffineSectionLie
open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
  (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X)
  {k : Type} [Field k] (q : Spec (.of k) ⟶ X)

def conormalEquiv :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := baseFieldAlgebra q
    Space p s q ≃ₗ[k] ((RingHom.ker s.appTop.hom).Cotangent →ₗ[Γ(X, ⊤)] k) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := baseFieldAlgebra q
  let := ambientFieldAlgebra s q
  let := fieldScalarTower p s q hs
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.quotientAlgebra s
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.scalarTower p s hs
  let : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.sectionRing_smooth p
  exact (algebraEquiv p s hs q).trans (Relative.DualLifts.RelativeDualLifts.conormalEquiv Γ(X, ⊤) Γ(Y, ⊤) k)

theorem conormalEquiv_toCotangent (v : Space p s q) (b : RingHom.ker s.appTop.hom) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
    letI := baseFieldAlgebra q
    conormalEquiv p s hs q v (Ideal.toCotangent _ b) =
      (v.val.hom (Y.presheaf.Γgerm ((zeroPoint s q) (IsLocalRing.closedPoint (DualNumber k))) b)).snd := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra p
  let := baseFieldAlgebra q
  let := ambientFieldAlgebra s q
  let := fieldScalarTower p s q hs
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.quotientAlgebra s
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.scalarTower p s hs
  let : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.sectionRing_smooth p
  change Relative.DualLifts.RelativeDualLifts.conormalEquiv Γ(X, ⊤) Γ(Y, ⊤) k (algebraEquiv p s hs q v)
    (Ideal.toCotangent _ b) = _
  rw [Relative.DualLifts.RelativeDualLifts.conormalEquiv_toCotangent, algebraEquiv_hom]

end AffineSectionLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.SectionLie
