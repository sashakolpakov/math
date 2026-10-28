import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberCharts
import OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Fiber Chart Projection -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FiberChartProjection.Abelian.RelativeCharts

noncomputable section

section

/-!
Lift constructed affine relative product charts through genuine affine
open immersions to native scheme points. The actual projection identity
is proved from the commuting scheme diagram, then sliced on the actual
scheme base-change fiber.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical ContDiff

variable {R A E F : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A}

/-- The actual smooth scheme morphism makes the affine relative algebra
smooth. This is derived from the affine open diagram and the spectrum
criterion, so algebra smoothness is not an additional family hypothesis. -/
theorem algebraSmooth_of_nativeDiagram
    (p : X ⟶ S) [Smooth p.left]
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (hi : i ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b) :
    Algebra.Smooth R A := by
  let f := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A)
  have heq : i.left ≫ p.left = f.left ≫ b.left := congrArg Over.Hom.left hi
  have hcomp : Smooth (f.left ≫ b.left) := by
    rw [← heq]
    infer_instance
  have hpb : IsPullback (𝟙 (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left) f.left
      (f.left ≫ b.left) b.left :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  have hsm : Smooth f.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hcomp
  have hring : (algebraMap R A).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm
  exact RingHom.smooth_algebraMap.mp hring

/-- From smoothness of the genuine family and a standard-smooth affine
base chart, construct the relative presentation and product charts. -/
theorem exists_relative_charts_from_smooth_scheme
    {I Sigma : Type} [Fintype I] [Fintype Sigma]
    (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    (p : X ⟶ S) [Smooth p.left]
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (hi : i ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ D : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.RelativePresentationAt (R := R) x,
      Nonempty (SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x
        (Prod.fst : (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) ×
          (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates D.presentation.map → ℂ) → (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ))) := by
  let : Algebra.Smooth R A := algebraSmooth_of_nativeDiagram p b i hi
  exact RelativePointOpenness.Abelian.RelativeCharts.exists_smooth_relative_product_charts P x

theorem nativeAffinePoint_base
    (p : X ⟶ S) (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    (hi : i ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i y) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b
        (y.comp (IsScalarTower.toAlgHom ℂ R A)) := by
  rw [← AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp, hi]
  exact AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap (CommAlgCat.of ℂ R) (CommAlgCat.of ℂ A)
    (IsScalarTower.toAlgHom ℂ R A) b y

/-- Actual affine chart lifts intertwine the native scheme projection
with first-coordinate projection. No compatibility premise is added. -/
theorem native_relative_chart_projection
    (p : X ⟶ S) (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (hi : i ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F))
    (q : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hq : q ∈ (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i C.total).source) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p q ∈ (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ R) b C.base).source ∧
      (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i C.total q).1 =
        AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ R) b C.base (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p q) := by
  obtain ⟨y, hy, rfl⟩ := hq
  have hb : y.comp (IsScalarTower.toAlgHom ℂ R A) ∈ C.base.source := by
    simpa only [C.total.left_inv hy] using C.mapsTo _ (C.total.map_source hy)
  have hp : (C.total y).1 = C.base (y.comp (IsScalarTower.toAlgHom ℂ R A)) := by
    simpa only [C.total.left_inv hy] using (C.projection _ (C.total.map_source hy)).symm
  rw [nativeAffinePoint_base p b i hi]
  constructor
  · exact ⟨y.comp (IsScalarTower.toAlgHom ℂ R A), hb, rfl⟩
  · change ((C.total.lift_openEmbedding (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap (CommAlgCat.of ℂ A) i))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i y)).1 =
        (C.base.lift_openEmbedding (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap (CommAlgCat.of ℂ R) b))
          (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b
            (y.comp (IsScalarTower.toAlgHom ℂ R A)))
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply,
      OpenPartialHomeomorph.lift_openEmbedding_apply]
    exact hp

/-- A constructed affine relative chart gives a chart on the actual
scheme fiber at its central point. Both directions agree with the native
total chart and the genuine fiber inclusion. -/
theorem exists_schemeFiber_chart_from_relative
    (p : X ⟶ S) (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (hi : i ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F)) :
    let q := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x
    let s := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p q
    ∃ (q₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AbelianFamilyPoints.FamilyPoints.fiber p s))
      (c : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AbelianFamilyPoints.FamilyPoints.fiber p s)) E),
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) q₀ = q ∧ q₀ ∈ c.source ∧
      (∀ y, c y = (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i C.total
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) y)).2) ∧
      ∀ v ∈ c.target,
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) (c.symm v) =
          (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i C.total).symm
            (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ R) b C.base s, v) := by
  dsimp only
  let q := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x
  let s := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p q
  let H := AbelianFamilyPoints.FamilyPoints.fiberHomeomorph p s
  let q₀ := H.symm ⟨q, rfl⟩
  have hq₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) q₀ = q :=
    congrArg Subtype.val (H.apply_symm_apply ⟨q, rfl⟩)
  let e := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i C.total
  let eb := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ R) b C.base
  have hq : q ∈ e.source := ⟨x, C.point, rfl⟩
  have hprojection := native_relative_chart_projection p b i hi C
  have hb : s ∈ eb.source := (hprojection q hq).1
  have hinc : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) q₀ ∈ e.source := by
    rw [hq₀]
    exact hq
  obtain ⟨c, hc, _, hf, hinv⟩ := IntrinsicFiberCharts.Abelian.FamilyPoints.exists_native_fiber_chart p s q₀ eb e hb hinc
    (fun y hy => (hprojection y hy).1) (fun y hy => (hprojection y hy).2)
  exact ⟨q₀, c, hq₀, hc, hf, hinv⟩

end

/-!
The total relative chart has the specified base coordinate on every
actual point of the literal scheme fiber, including exponential images.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical

variable {R A E F : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A}

theorem native_fiber_chart_base_coordinate
    (p : X ⟶ S) (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (hi : i ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F))
    (q : F) (hq : q ∈ C.base.target)
    (z : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AbelianFamilyPoints.FamilyPoints.fiber p
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (C.base.symm q))))
    (hz : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (C.base.symm q))) z ∈
        (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i C.total).source) :
    (AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart (CommAlgCat.of ℂ A) i C.total
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (C.base.symm q))) z)).1 = q := by
  let s := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (C.base.symm q)
  have hp : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianFamilyPoints.FamilyPoints.fiberInclusion p s) z) = s :=
    (AbelianFamilyPoints.FamilyPoints.fiberHomeomorph p s z).property
  have h := (native_relative_chart_projection p b i hi C _ hz).2
  rw [hp] at h
  apply h.trans
  change (C.base.lift_openEmbedding (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap (CommAlgCat.of ℂ R) b))
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ R) b (C.base.symm q)) = q
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply, C.base.right_inv hq]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FiberChartProjection.Abelian.RelativeCharts
