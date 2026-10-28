import OAI.RepresentationTheory.Hecke.Rational
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Interface
import OAI.RepresentationTheory.Theta.Geometric.TateComparison
import OAI.RepresentationTheory.Theta.Geometric.ComponentVarieties
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe

/-! # Betti -/

namespace OAI.RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic

noncomputable section

/-! The actual full rational Betti space and its Hecke action.
The geometric projective presentation proves finite dimensionality.
The complete native CentralAction conclusion supplies both central power identities;
their scalar-extension compatibility is proved on the tensor product.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

/-- The actual Betti space, with its additive and scalar instances cached
under a short name to avoid repeatedly unfolding categorical cohomology. -/
def RationalBetti : Type := D.H1

instance : AddCommGroup (RationalBetti D) := inferInstanceAs (AddCommGroup D.H1)
instance : Module ℚ (RationalBetti D) := inferInstanceAs (Module ℚ D.H1)

def rationalAction (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ (RationalBetti D) :=
  A.rhoH1

def nativeFullAction (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) :
    ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] Module.End ℂ (ℂ ⊗[ℚ] RationalBetti D) :=
  Rational.CentralConstraintIntrinsic.scalarExtendedAction (H := AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) (V := RationalBetti D) (rationalAction D A)

theorem nativeFullAction_tmul (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) (c : ℂ) (h : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :
    nativeFullAction D A (c ⊗ₜ[ℚ] h) = c • (rationalAction D A h).baseChange ℂ := rfl

theorem rationalAction_power (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) (h : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) (n : ℕ)
    (hn : (A.rhoH1 h) ^ n = 1) : (rationalAction D A h) ^ n = 1 := hn

def actionProjection (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) : Theta.Geometric.TateComparison.Action D :=
  ⟨A.basis, A.markingShift, A.TAlb, A.rho, A.rhoH1⟩

theorem actionProjection_realizes
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hTateComparison : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A) :
    (actionProjection D A).IsRealization D hg hq hIsogenyQuotient :=
  ⟨hTateComparison.flags, hTateComparison.raw, hTateComparison.scalarIsogeny, hTateComparison.scalarGraph,
    hTateComparison.integral, hTateComparison.scalarUnit, hTateComparison.pointPush, hTateComparison.cohomology, hTateComparison.forms⟩

def integralBettiPullback (a : D.EndK) : Module.End ℚ (RationalBetti D) :=
  D.pullbackH1Integral a

theorem rationalAction_geometric_clear
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hTateComparison : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (h : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) (n : ℕ) (hn : 0 < n) (a : D.EndK)
    (hclear : n • A.rho h = D.toRational a) :
    (n : ℚ) • rationalAction D A h = integralBettiPullback D a :=
  (hTateComparison.cohomology h).2 n hn a hclear

/-- Scalar extension agrees with the genuine geometric pullback after
every valid denominator clearing, not an assumed comparison equation. -/
theorem nativeFullAction_geometric_pullback
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hTateComparison : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (h : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) (n : ℕ) (hn : 0 < n) (a : D.EndK)
    (hclear : n • A.rho h = D.toRational a) :
    (n : ℂ) • nativeFullAction D A (1 ⊗ₜ[ℚ] h) =
      (integralBettiPullback D a).baseChange ℂ := by
  rw [nativeFullAction_tmul, one_smul]
  have heq := congrArg (fun f : Module.End ℚ (RationalBetti D) => f.baseChange ℂ)
    (rationalAction_geometric_clear D hg hq hIsogenyQuotient A hTateComparison h n hn a hclear)
  rw [Rational.CentralConstraintIntrinsic.rational_baseChange_nat_smul] at heq
  exact heq

def bettiProjectivePresentation (hg : D.HasIntegralModelGeometry) : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := ((Over.pullback D.complexPoint).obj D.model.space).left
  structureMap := ((Over.pullback D.complexPoint).obj D.model.space).hom
  projective := Theta.Geometric.ComponentVarieties.RelativeProjective.complexProjectivePresentation
    (Classical.choice hg.projective) D.complexPoint
  smooth := by
    let : Smooth D.model.space.hom := hg.smooth
    dsimp
    infer_instance

def bettiAlbaneseBaseChangeIso :
    (Over.pullback D.complexPoint).obj D.components.product ≅ D.complexAlbanese.X :=
  ((Over.pullback D.complexPoint).mapIso
    (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProductComparison D.components.A)).symm ≪≫
      (Over.pullbackComp D.complexGenericPoint D.generic).app
        (AlgebraicGeometry.AbelianScheme.TateComparison.Products.componentProduct D.components.A).X

theorem rationalBetti_finite (hg : D.HasIntegralModelGeometry) :
    FiniteDimensional ℚ (RationalBetti D) := by
  let : IsIso D.componentAssembly := hg.decomposition
  let : FiniteDimensional ℚ
      (AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiQ ((Over.pullback D.complexPoint).obj D.model.space) 1) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_cohomology_finite
      (bettiProjectivePresentation D hg) 1
  let f := D.components.totalComplexMap D.complexPoint (asIso D.componentAssembly)
  let b := ((AlgebraicGeometry.Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) 1).mapIso
    (bettiAlbaneseBaseChangeIso D).op).toLinearEquiv
  exact Module.Finite.of_injective ((AlgebraicGeometry.PELModuli.IntegralModel.Product.bettiPullbackQ f 1).comp b.toLinearMap)
    (hg.betti.1.comp b.injective)

theorem native_rational_eigenvalues_algebraic
    (hg : D.HasIntegralModelGeometry) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (h : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) : IsAlgebraic ℚ (χ (1 ⊗ₜ[ℚ] h)) := by
  let := rationalBetti_finite D hg
  apply Rational.CentralConstraintIntrinsic.rational_generalized_eigenvalue_algebraic (V := RationalBetti D)
    (rationalAction D A h)
  have hi : (nativeFullAction D A (1 ⊗ₜ[ℚ] h)).genEigenspace
      (χ (1 ⊗ₜ[ℚ] h)) ⊤ ≠ ⊥ := by
    intro hz
    apply hχ
    apply le_antisymm _ bot_le
    rw [← hz]
    exact iInf_le _ (1 ⊗ₜ[ℚ] h)
  simpa only [nativeFullAction_tmul, one_smul] using hi

/-- Exactly the complete conclusion of native CentralAction for these objects. -/
def Conclusion (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) (active : Fin s) (fullSide : Fin s → Bool) : Prop :=
  ∃ (σT σC : Aut D.space),
    AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.CorrespondenceIsGraph (D.correspondence (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.clearedT3Type active)) (σT ≪≫ A.markingShift) ∧
    AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.CorrespondenceIsGraph (D.correspondence (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0IntegralType active fullSide)) σC ∧
    ∃ n : ℕ, 0 < n ∧ σT ^ n = 1 ∧ σC ^ n = 1 ∧
      (A.rho (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q active)) ^ n = 1 ∧
      (A.rho (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q active fullSide)) ^ n = 1 ∧
      (A.rhoH1 (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q active)) ^ n = 1 ∧
      (A.rhoH1 (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q active fullSide)) ^ n = 1

theorem native_central_scalar_extension
    (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) (active : Fin s) (fullSide : Fin s → Bool)
    (hCentralAction : Conclusion D A active fullSide) :
    ∃ n : ℕ, 0 < n ∧
      (nativeFullAction D A (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q active)) ^ n = 1 ∧
      (nativeFullAction D A (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q active fullSide)) ^ n = 1 := by
  obtain ⟨_, _, _, _, n, hn, _, _, _, _, hT, hC⟩ := hCentralAction
  refine ⟨n, hn, ?_, ?_⟩
  · rw [nativeFullAction_tmul, one_smul, ← LinearMap.baseChange_pow,
      rationalAction_power D A _ n hT, LinearMap.baseChange_one]
  · rw [nativeFullAction_tmul, one_smul, ← LinearMap.baseChange_pow,
      rationalAction_power D A _ n hC, LinearMap.baseChange_one]

end

end OAI.RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic
