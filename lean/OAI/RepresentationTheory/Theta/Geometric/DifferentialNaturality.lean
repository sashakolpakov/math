import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Branches
import OAI.RepresentationTheory.Theta.Geometric.LinearTheta

/-! # Differential Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.DifferentialNaturality

noncomputable section

section

/-!
Canonical realization of algebraic differentials in period coordinates.
The realization is the universal Kähler lift of ordinary differentiation;
it is not an independently supplied comparison map. TateComparison's trace equation
therefore gives a sum of actual differentiated affine branch values.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Branches

/-- Coordinate functions differentiable at the specified period point. -/
def functionsAt (x : LinearTheta.BallCoordinates) : Subalgebra ℂ (LinearTheta.BallCoordinates → ℂ) where
  carrier := {f | DifferentiableAt ℂ f x}
  zero_mem' := differentiableAt_const 0
  one_mem' := differentiableAt_const 1
  add_mem' := fun hf hg => hf.add hg
  mul_mem' := fun hf hg => hf.mul hg
  algebraMap_mem' := fun c => differentiableAt_const c

def evaluateAt (x : LinearTheta.BallCoordinates) : functionsAt x →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ : LinearTheta.BallCoordinates => ℂ) x).comp (functionsAt x).val

instance cotangentFunctionModule (x : LinearTheta.BallCoordinates) : Module (functionsAt x) LinearTheta.Cotangent :=
  Module.compHom LinearTheta.Cotangent (evaluateAt x).toRingHom

instance cotangentFunctionTower (x : LinearTheta.BallCoordinates) :
    IsScalarTower ℂ (functionsAt x) LinearTheta.Cotangent where
  smul_assoc c f v := by
    change (c * f.val x) • v = c • (f.val x • v)
    exact mul_smul c (f.val x) v

/-- Ordinary differentiation is a derivation of the actual coordinate algebra. -/
def periodDerivation (x : LinearTheta.BallCoordinates) : Derivation ℂ (functionsAt x) LinearTheta.Cotangent where
  toFun f := fderiv ℂ f.val x
  map_add' f g := fderiv_add f.property g.property
  map_smul' c f := fderiv_const_smul f.property c
  map_one_eq_zero' := by
    change fderiv ℂ (fun _ : LinearTheta.BallCoordinates => (1 : ℂ)) x = 0
    simp
  leibniz' f g := fderiv_mul f.property g.property

/-- The Kähler differential of a coordinate function maps to its actual
complex derivative, by the universal property of Kähler differentials. -/
def periodDifferential (x : LinearTheta.BallCoordinates) :
    KaehlerDifferential ℂ (functionsAt x) →ₗ[ℂ] LinearTheta.Cotangent :=
  (periodDerivation x).liftKaehlerDifferential.restrictScalars ℂ

@[simp] theorem periodDifferential_D (x : LinearTheta.BallCoordinates) (f : functionsAt x) :
    periodDifferential x (KaehlerDifferential.D ℂ (functionsAt x) f) =
      fderiv ℂ f.val x :=
  (periodDerivation x).liftKaehlerDifferential_comp_D f

abbrev periodTest (x : LinearTheta.BallCoordinates) : CommAlgCat.{0} ℂ := .of ℂ (functionsAt x)

/-- The algebraic form is evaluated on an actual affine test map and then
differentiated. No input-to-form or pullback compatibility is assumed. -/
def formInPeriodCoordinates {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x : LinearTheta.BallCoordinates) (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (periodTest x) ⟶ X) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X →ₗ[ℂ] LinearTheta.Cotangent where
  toFun ω := periodDifferential x (ω.val (periodTest x) p)
  map_add' _ _ := (periodDifferential x).map_add _ _
  map_smul' c _ := (periodDifferential x).map_smul c _

/-- The explicit TateComparison trace equation passes to the canonical period
differentials on every actual affine branch splitting. -/
theorem trace_in_period_coordinates
    {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence X)
    (ω η : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X) (h_TateComparison : AlgebraicGeometry.AbelianScheme.TateComparison.Branches.IsBranchTrace C ω η)
    (x : LinearTheta.BallCoordinates) (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (periodTest x) ⟶ X)
    (n : ℕ) (e : C.BranchSplitting p n) :
    formInPeriodCoordinates x p η =
      ∑ i : Fin n, formInPeriodCoordinates x (C.endpoint (C.splitBranch p e i)) ω := by
  change periodDifferential x (η.val (periodTest x) p) = _
  rw [h_TateComparison (periodTest x) p n e, map_sum]
  rfl

end

/-! The period realization of Kähler forms obeys the actual analytic chain
rule. Both maps in the comparison are constructed, and naturality is proved
on universal differentials and extended to their full module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Branches

@[simp] theorem differentialMap_D {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S) (r : R) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.differentialMap f (KaehlerDifferential.D ℂ R r) =
      KaehlerDifferential.D ℂ S (f.hom r) := by
  let : Algebra R S := f.hom.toAlgebra
  let : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq
    (fun x => (f.hom.commutes x).symm)
  change KaehlerDifferential.map ℂ ℂ R S (KaehlerDifferential.D ℂ R r) = _
  exact KaehlerDifferential.map_D ℂ ℂ R S r

theorem differentialMap_smul {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S)
    (r : R) (ω : KaehlerDifferential ℂ R) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.differentialMap f (r • ω) = f.hom r • AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.differentialMap f ω := by
  let : Algebra R S := f.hom.toAlgebra
  let : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq
    (fun x => (f.hom.commutes x).symm)
  change KaehlerDifferential.map ℂ ℂ R S (r • ω) =
    f.hom r • KaehlerDifferential.map ℂ ℂ R S ω
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul S r _).symm

theorem periodDifferential_smul (x : LinearTheta.BallCoordinates)
    (f : functionsAt x) (ω : KaehlerDifferential ℂ (functionsAt x)) :
    periodDifferential x (f • ω) = f.val x • periodDifferential x ω :=
  (periodDerivation x).liftKaehlerDifferential.map_smul f ω

/-- The coordinate-ring map is actual substitution by the analytic map. -/
def functionSubstitution (f : LinearTheta.BallCoordinates → LinearTheta.BallCoordinates)
    (x : LinearTheta.BallCoordinates) (hf : DifferentiableAt ℂ f x) :
    functionsAt (f x) →ₐ[ℂ] functionsAt x where
  toFun g := ⟨g.val ∘ f, g.property.comp x hf⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

abbrev substitutionHom (f : LinearTheta.BallCoordinates → LinearTheta.BallCoordinates)
    (x : LinearTheta.BallCoordinates) (hf : DifferentiableAt ℂ f x) :
    periodTest (f x) ⟶ periodTest x :=
  CommAlgCat.ofHom (functionSubstitution f x hf)

/-- The algebraic Kähler pullback becomes the ordinary cotangent pullback.
This is derived from the chain rule, not an input comparison equation. -/
theorem periodDifferential_substitution
    (f : LinearTheta.BallCoordinates → LinearTheta.BallCoordinates) (x : LinearTheta.BallCoordinates)
    (hf : DifferentiableAt ℂ f x)
    (ω : KaehlerDifferential ℂ (functionsAt (f x))) :
    periodDifferential x (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.differentialMap (substitutionHom f x hf) ω) =
      (periodDifferential (f x) ω).comp (fderiv ℂ f x) := by
  have hspan : ω ∈ Submodule.span (functionsAt (f x))
      (Set.range (KaehlerDifferential.D ℂ (functionsAt (f x)))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hspan
  · rintro _ ⟨g, rfl⟩
    rw [differentialMap_D, periodDifferential_D, periodDifferential_D]
    exact fderiv_comp x g.property hf
  · simp only [map_zero, ContinuousLinearMap.zero_comp]
  · intro a b _ _ ha hb
    simp only [map_add, ContinuousLinearMap.add_comp, ha, hb]
  · intro c a _ ha
    rw [differentialMap_smul, periodDifferential_smul, periodDifferential_smul, ha]
    rfl

@[simp] theorem formInPeriodCoordinates_pullback
    {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (F : X ⟶ Y)
    (x : LinearTheta.BallCoordinates) (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (periodTest x) ⟶ X)
    (ω : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms Y) :
    formInPeriodCoordinates x p (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback F ω) =
      formInPeriodCoordinates x (p ≫ F) ω := rfl

/-- Coordinate substitution for an actual global algebraic one-form.
Its functor-of-points naturality and the proved chain rule suffice. -/
theorem formInPeriodCoordinates_substitution
    {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : LinearTheta.BallCoordinates → LinearTheta.BallCoordinates) (x : LinearTheta.BallCoordinates)
    (hf : DifferentiableAt ℂ f x)
    (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (periodTest (f x)) ⟶ X) (ω : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X) :
    formInPeriodCoordinates x (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (substitutionHom f x hf) ≫ p) ω =
      (formInPeriodCoordinates (f x) p ω).comp (fderiv ℂ f x) := by
  change periodDifferential x
    (ω.val (periodTest x) (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (substitutionHom f x hf) ≫ p)) = _
  rw [← ω.property (periodTest (f x)) (periodTest x) (substitutionHom f x hf) p]
  exact periodDifferential_substitution f x hf _

end

end OAI.RepresentationTheory.Theta.Geometric.DifferentialNaturality
