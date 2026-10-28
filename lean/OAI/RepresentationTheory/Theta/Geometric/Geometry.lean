import OAI.RepresentationTheory.Theta.Geometric.Data
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Hecke
import OAI.RepresentationTheory.Theta.Geometric.Complexify
import OAI.AlgebraicGeometry.Betti.ProjectiveCohomology

/-! # Geometry -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Native geometric objects in GeometricTheta's conclusion. Period covers, algebraic
theta lifts, and rational pullbacks are properties to prove, not record
fields. Cleared branches retain their actual correspondence-cover lifts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold

def Geometry.productCoordinateIdempotent {B : Scheme} {r : ℕ}
    (A : Fin r → CommGrp (Over B)) (j : Fin r) :
    (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProduct A).X ⟶ (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProduct A).X :=
  (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductComparison A).hom ≫
    (Pi.lift fun i => if i = j then Pi.π (fun k => (A k).X) i else 1) ≫
      (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductComparison A).inv

theorem Geometry.conjugate_idempotent {C : Type*} [Category C] {X Y : C}
    (e : X ≅ Y) (p : Y ⟶ Y) (hp : p ≫ p = p) :
    (e.hom ≫ p ≫ e.inv) ≫ (e.hom ≫ p ≫ e.inv) = e.hom ≫ p ≫ e.inv := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc p p, hp]

theorem Geometry.productCoordinateIdempotent_comp {B : Scheme} {r : ℕ}
    (A : Fin r → CommGrp (Over B)) (j : Fin r) :
    Geometry.productCoordinateIdempotent A j ≫ Geometry.productCoordinateIdempotent A j =
      Geometry.productCoordinateIdempotent A j := by
  apply Geometry.conjugate_idempotent
  apply Pi.hom_ext
  intro i
  by_cases h : i = j <;> simp [Category.assoc, h]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

abbrev Data.ActiveHeckeThetaData.componentComplex (j : Fin D.pel.componentCount) :=
  (Over.pullback D.pel.complexGenericPoint).obj (D.pel.componentGeneric j)

abbrev Data.ActiveHeckeThetaData.componentComplexInclusion (j : Fin D.pel.componentCount) :=
  (Over.pullback D.pel.complexGenericPoint).map (D.pel.componentInclusion j)

def Data.ActiveHeckeThetaData.ballH1Projector (j : Fin D.pel.componentCount) : Module.End ℚ D.pel.H1 :=
  AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ
    ((Over.pullback D.pel.complexGenericPoint).map
      ((Over.pullback D.pel.generic).map
        (Geometry.productCoordinateIdempotent D.pel.components.A j))) 1

def Data.ActiveHeckeThetaData.IsPeriodUniformization
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (c : D.domain → X.analyticSpace) : Prop :=
  Function.Surjective c ∧ IsCoveringMap c ∧
  MDifferentiable 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) c ∧
  (∀ x, Function.Bijective
    (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) c x)) ∧
  ∀ x y, c x = c y ↔ ∃ g : D.RationalSU,
    D.rationalFinite g ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup ∧
      y.val = D.periodMap g x.val

def Data.ActiveHeckeThetaData.totalPeriodMap (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : X.toOver ≅ D.componentComplex j) (c : D.domain → X.analyticSpace) :
    D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace :=
  fun x => c x ≫ e.hom ≫ D.componentComplexInclusion j

def Data.ActiveHeckeThetaData.periodTestPoint {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (x y : LinearTheta.BallCoordinates)
    (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x) ⟶ X) : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X :=
  AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (DifferentialNaturality.functionsAt x)
    ((Pi.evalAlgHom ℂ (fun _ : LinearTheta.BallCoordinates => ℂ) y).comp (DifferentialNaturality.functionsAt x).val) ≫ p

/-- This affine test has precisely the specified period-map germ on
complex points. Its existence is part of the conclusion to construct. -/
def Data.ActiveHeckeThetaData.IsPeriodChartAt (c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (x : D.domain) (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ D.pel.complexSpace) : Prop :=
  ∀ᶠ y in nhds x.val, ∀ hy : y ∈ D.domain,
    Data.ActiveHeckeThetaData.periodTestPoint x.val y p = c ⟨y, hy⟩

/-- Equality with the canonical theta form on all actual period charts,
and extension by zero on every complementary algebraic component. This
property is a conclusion for the constructed Albanese-form lift. -/
def Data.ActiveHeckeThetaData.IsCanonicalThetaLift (hgeometry : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount)
    (c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) : Prop :=
  (∀ x : D.domain, ∃ p, D.IsPeriodChartAt c x p) ∧
  (∀ (φ : D.sphericalInputs) (x : D.domain)
      (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ D.pel.complexSpace),
    D.IsPeriodChartAt c x p →
      DifferentialNaturality.formInPeriodCoordinates x.val p (D.pel.albanesePullback hgeometry (Θ φ)) =
        D.thetaUniversal φ.val x.val) ∧
  ∀ (i : Fin D.pel.componentCount), i ≠ j → ∀ φ : D.sphericalInputs,
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.componentComplexInclusion i)
      (D.pel.albanesePullback hgeometry (Θ φ)) = 0

def Data.ActiveHeckeThetaData.IsRationalFormsPullback (a : D.pel.EndQ)
    (f : Module.End ℂ D.pel.OneFormsA) : Prop :=
  (∃ (n : ℕ), 0 < n ∧ ∃ b : D.pel.EndK, n • a = D.pel.toRational b) ∧
  ∀ (n : ℕ), 0 < n → ∀ b : D.pel.EndK, n • a = D.pel.toRational b →
    (n : ℂ) • f = D.pel.pullbackForms b

structure Data.ActiveHeckeThetaData.ClearedBranch
    (c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace) (a : Intrinsic.Hecke.ActiveWeight) where
  lift : C(D.domain, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
    (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).cover)
  source : ∀ x, lift x ≫
    (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).source = c x

def Data.ActiveHeckeThetaData.clearedBranchTarget (shift : D.pel.space ≅ D.pel.space)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} {a : Intrinsic.Hecke.ActiveWeight}
    (b : D.ClearedBranch c a) (x : D.domain) : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace :=
  (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((Over.pullback D.pel.complexGenericPoint).map shift.inv))^[
    Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a]
    (b.lift x ≫
      (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target)

end

end OAI.RepresentationTheory.Theta.Geometric
