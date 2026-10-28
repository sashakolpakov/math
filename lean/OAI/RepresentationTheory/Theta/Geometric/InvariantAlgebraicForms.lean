import OAI.RepresentationTheory.Theta.Geometric.GroupJetCoordinates
import OAI.RepresentationTheory.Theta.Geometric.PointCotangent

/-! # Invariant Algebraic Forms -/

namespace OAI.RepresentationTheory.Theta.Geometric.InvariantAlgebraicForms

noncomputable section

/-! Covectors at the identity give actual algebraic one-forms: their
values are Kähler differentials on every affine test scheme, and the
compatibility condition is proved from the universal group jet. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.MonObj

attribute [local instance] Universal.DifferentialJet.differentialOppositeModule

variable {G U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj G] [IsAffine U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left]
    (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U) (he : e ≫ i = 1)

@[instance_reducible] def identityChartPointAlgebra : Algebra Γ(U.left, ⊤) ℂ :=
  (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e).toRingHom.toAlgebra

variable [Algebra Γ(U.left, ⊤) ℂ] [IsScalarTower ℂ Γ(U.left, ⊤) ℂ]
    (hscalar : ∀ a : Γ(U.left, ⊤), algebraMap Γ(U.left, ⊤) ℂ a = AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e a)

abbrev identityChartCotangent (U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine U.left]
    [Algebra Γ(U.left, ⊤) ℂ] :=
  PointCotangent.pointCotangent ℂ Γ(U.left, ⊤)

def identityCotangentTestValue (R : CommAlgCat.{0} ℂ) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    identityChartCotangent U →ₗ[ℂ] KaehlerDifferential ℂ R := by
  letI : CommRing (Universal.DifferentialJet.differentialJetRing R) := inferInstance
  letI : Algebra ℂ (Universal.DifferentialJet.differentialJetRing R) := inferInstance
  letI : Module Γ(U.left, ⊤) (KaehlerDifferential ℂ R) :=
    Module.compHom _ (algebraMap Γ(U.left, ⊤) ℂ)
  letI : IsScalarTower Γ(U.left, ⊤) ℂ (KaehlerDifferential ℂ R) :=
    IsScalarTower.of_compHom _ _ _
  letI : IsScalarTower ℂ Γ(U.left, ⊤) (KaehlerDifferential ℂ R) := by
    constructor
    intro c a v
    change algebraMap Γ(U.left, ⊤) ℂ (c • a) • v =
      c • (algebraMap Γ(U.left, ⊤) ℂ a • v)
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_smul]
  let δ : Derivation ℂ Γ(U.left, ⊤) (KaehlerDifferential ℂ R) := {
    toFun a := (GroupJetCoordinates.universalGroupJetCoordinates i e he R x a).snd
    map_add' a b := by rw [map_add, TrivSqZeroExt.snd_add]
    map_smul' c a := by rw [map_smul, TrivSqZeroExt.snd_smul]; rfl
    map_one_eq_zero' := by
      change (GroupJetCoordinates.universalGroupJetCoordinates i e he R x 1).snd = 0
      rw [map_one]; rfl
    leibniz' a b := by
      change (GroupJetCoordinates.universalGroupJetCoordinates i e he R x (a * b)).snd = _
      rw [map_mul, TrivSqZeroExt.snd_mul]
      change (GroupJetCoordinates.universalGroupJetCoordinates i e he R x a).fst •
          (GroupJetCoordinates.universalGroupJetCoordinates i e he R x b).snd +
        (GroupJetCoordinates.universalGroupJetCoordinates i e he R x b).fst •
          (GroupJetCoordinates.universalGroupJetCoordinates i e he R x a).snd = _
      rw [GroupJetCoordinates.universalGroupJetCoordinates_fst, GroupJetCoordinates.universalGroupJetCoordinates_fst,
        IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul,
        ← hscalar a, ← hscalar b]
      rfl }
  exact PointCotangent.pointDerivationEquiv ℂ Γ(U.left, ⊤) (KaehlerDifferential ℂ R) δ

set_option backward.isDefEq.respectTransparency false in
theorem identityCotangentTestValue_D (R : CommAlgCat.{0} ℂ)
    (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) (a : Γ(U.left, ⊤)) :
    identityCotangentTestValue i e he hscalar R x
      (1 ⊗ₜ[Γ(U.left, ⊤)] KaehlerDifferential.D ℂ Γ(U.left, ⊤) a) =
      (GroupJetCoordinates.universalGroupJetCoordinates i e he R x a).snd := by
  unfold identityCotangentTestValue
  rw [PointCotangent.pointDerivationEquiv_D]
  rfl

theorem identityCotangentTestValue_naturality {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S)
    (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.differentialMap f).comp (identityCotangentTestValue i e he hscalar R x) =
      identityCotangentTestValue i e he hscalar S (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap f ≫ x) := by
  let : Module Γ(U.left, ⊤) (KaehlerDifferential ℂ S) :=
    Module.compHom _ (algebraMap Γ(U.left, ⊤) ℂ)
  let : IsScalarTower Γ(U.left, ⊤) ℂ (KaehlerDifferential ℂ S) :=
    IsScalarTower.of_compHom _ _ _
  let : IsScalarTower ℂ Γ(U.left, ⊤) (KaehlerDifferential ℂ S) := by
    constructor
    intro c a v
    change algebraMap Γ(U.left, ⊤) ℂ (c • a) • v =
      c • (algebraMap Γ(U.left, ⊤) ℂ a • v)
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_smul]
  apply PointCotangent.pointCotangent_linearMap_ext ℂ Γ(U.left, ⊤)
  intro a
  rw [LinearMap.comp_apply, identityCotangentTestValue_D, identityCotangentTestValue_D]
  exact congrArg TrivSqZeroExt.snd
    (AlgHom.congr_fun (GroupJetCoordinates.universalGroupJetCoordinates_naturality i e he f x) a)

def identityCotangentOneForm : identityChartCotangent U →ₗ[ℂ] AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms G where
  toFun a := ⟨fun R x => identityCotangentTestValue i e he hscalar R x a, by
    intro R S f x
    exact LinearMap.congr_fun (identityCotangentTestValue_naturality i e he hscalar f x) a⟩
  map_add' a b := by
    apply Subtype.ext
    funext R x
    exact map_add (identityCotangentTestValue i e he hscalar R x) a b
  map_smul' c a := by
    apply Subtype.ext
    funext R x
    exact map_smul (identityCotangentTestValue i e he hscalar R x) c a

end

end OAI.RepresentationTheory.Theta.Geometric.InvariantAlgebraicForms
