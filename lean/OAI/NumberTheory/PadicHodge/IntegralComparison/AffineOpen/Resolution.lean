import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactOpenRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SpecHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ProjectiveResolutionTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasicoherentTruncation
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-! # Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.Resolution

noncomputable section

/-! Restricting the genuine negative-twist resolution to an affine
coordinate subopen gives a projective resolution of the actual section
module of the original sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

instance chart_additive : (InternalHom.chartFunctor U hU).Additive := by
  unfold InternalHom.chartFunctor
  infer_instance

instance chart_preservesFiniteLimits : PreservesFiniteLimits (InternalHom.chartFunctor U hU) := by
  unfold InternalHom.chartFunctor
  infer_instance

instance chart_preservesFiniteColimits : PreservesFiniteColimits (InternalHom.chartFunctor U hU) := by
  unfold InternalHom.chartFunctor
  infer_instance

instance chart_preservesHomology : (InternalHom.chartFunctor U hU).PreservesHomology := inferInstance

theorem quasiIso {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex X.Modules c}
    (f : K ⟶ L) [∀ n, (K.X n).IsQuasicoherent] [∀ n, (L.X n).IsQuasicoherent]
    [QuasiIso f] : QuasiIso (((InternalHom.sections U hU).mapHomologicalComplex c).map f) := by
  let F := (InternalHom.chartFunctor U hU).mapHomologicalComplex c
  let (n : ι) : ((F.obj K).X n).IsQuasicoherent := InternalHom.chart_quasicoherent U hU (K.X n)
  let (n : ι) : ((F.obj L).X n).IsQuasicoherent := InternalHom.chart_quasicoherent U hU (L.X n)
  have : QuasiIso (F.map f) := inferInstance
  exact Affine.SpecHomology.quasiIso (F.map f)

theorem single_quasicoherent (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (((ChainComplex.single₀ X.Modules).obj M).X n).IsQuasicoherent := by
  by_cases hn : n = 0
  · subst n
    exact (AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent X).prop_of_iso
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0 M).symm inferInstance
  · exact QuasicoherentTruncation.of_isZero _
      (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 M n hn)

variable (M : X.Modules) [M.IsQuasicoherent] (K : ChainComplex X.Modules ℕ)
  [∀ n, (K.X n).IsQuasicoherent] (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M)
  [QuasiIso ε]

def ofAugmentation [∀ n, Projective ((InternalHom.sections U hU).obj (K.X n))] :
    ProjectiveResolution ((InternalHom.sections U hU).obj M) := by
  let (n : ℕ) : (((ChainComplex.single₀ X.Modules).obj M).X n).IsQuasicoherent :=
    single_quasicoherent M n
  let F := (InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)
  have : QuasiIso (F.map ε) := AffineOpen.Resolution.quasiIso U hU ε
  exact
    { complex := F.obj K
      projective n := inferInstanceAs (Projective ((InternalHom.sections U hU).obj (K.X n)))
      π := F.map ε ≫ (HomologicalComplex.singleMapHomologicalComplex (InternalHom.sections U hU) (.down ℕ) 0).hom.app M
      quasiIso := quasiIso_comp _ _ }

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

def negativeResolution (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (V : (Proj (homogeneousSubmodule σ R)).Opens) (hV : IsAffineOpen V)
    (i : σ) (hVi : V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (j : σ) (B : ℕ) :
    ProjectiveResolution ((InternalHom.sections V hV).obj M) := by
  let K := IntegralComparison.Projective.NegativeResolution.complex M j B
  let (n : ℕ) : (K.X n).IsQuasicoherent := inferInstanceAs
    ((IntegralComparison.Projective.NegativeResolution.presentation
      (IntegralComparison.Projective.NegativeResolution.state M j B n).module j B).source.IsQuasicoherent)
  let (n : ℕ) : Projective ((InternalHom.sections V hV).obj (K.X n)) :=
    Affine.ProjectiveResolutionTerms.term_projective V hV i hVi M j B n
  exact ofAugmentation V hV M K (IntegralComparison.Projective.NegativeResolution.augmentation M j B)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.Resolution
