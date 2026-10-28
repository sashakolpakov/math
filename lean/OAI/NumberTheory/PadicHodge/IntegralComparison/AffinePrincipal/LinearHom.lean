import OAI.NumberTheory.PadicHodge.IntegralComparison.LinearPurityBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Hom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LinearResolutionPurity
import Mathlib.RingTheory.Flat.Localization

/-! # Linear Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.LinearHom

noncomputable section

/-! The canonical linear Hom scalar-extension map is the original
principal-open restriction of the internal-Hom sheaf, on the full complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomEvaluation

theorem tensor_ext {R S M T : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup T] [Module S T]
    {f g : S ⊗[R] M →ₗ[S] T} (h : ∀ a m, f (a ⊗ₜ[R] m) = g (a ⊗ₜ[R] m)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a m => exact h a m

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) (r : Γ(X, U))

abbrev chartComplex (K : ChainComplex X.Modules ℕ) :=
  ((AffineOpen.InternalHom.sections U hU).mapHomologicalComplex (.down ℕ)).obj K

variable (N : X.Modules) [N.IsQuasicoherent] (K : ChainComplex X.Modules ℕ)
  [∀ i, (K.X i).IsQuasicoherent]
  [∀ i, Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  [∀ i, Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  [∀ i, ((Affine.LinearResolutionPurity.internalComplex N K).X i).IsQuasicoherent]
  (e : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

def targetFrame :
    (AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj N ≅
      ModuleCat.of Γ(X, Sections.openSubset U r) Γ(X, Sections.openSubset U r) :=
  LinearHomBaseChange.compatibleFrame Γ(X, U) Γ(X, Sections.openSubset U r) _ _ e
    (AffinePrincipal.Hom.Comparison.chartIso U hU r N)

def linearIso :
    ((PrincipalComplex.tensorFunctor U r).mapHomologicalComplex (.up ℕ)).obj
      (LinearHomBaseChange.homComplex Γ(X, U) (chartComplex U hU K)
        ((AffineOpen.InternalHom.sections U hU).obj N)) ≅
    LinearHomBaseChange.homComplex Γ(X, Sections.openSubset U r)
      (chartComplex (Sections.openSubset U r) (hU.basicOpen r) K)
      ((AffineOpen.InternalHom.sections (Sections.openSubset U r) (hU.basicOpen r)).obj N) := by
  let : IsLocalization.Away r Γ(X, Sections.openSubset U r) := hU.isLocalization_basicOpen r
  let : Module.Flat Γ(X, U) Γ(X, Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, Sections.openSubset U r) (Submonoid.powers r)
  let (i : ℕ) : Module.Free Γ(X, U) ((chartComplex U hU K).X i) :=
    inferInstanceAs (Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i)))
  let (i : ℕ) : Module.Finite Γ(X, U) ((chartComplex U hU K).X i) :=
    inferInstanceAs (Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i)))
  exact LinearHomBaseChange.complexIso Γ(X, U) Γ(X, Sections.openSubset U r)
    (chartComplex U hU K) (chartComplex (Sections.openSubset U r) (hU.basicOpen r) K)
    (PrincipalComplex.chartIso U hU r (.down ℕ) K) _ _ e (targetFrame U hU r N e)

omit [∀ i, Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i))]
  [∀ i, Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i))] in
theorem chart_component (i : ℕ) :
    (PrincipalComplex.chartIso U hU r (.down ℕ) K).hom.f i =
      (AffinePrincipal.Hom.Comparison.chartIso U hU r (K.X i)).hom := by
  apply ModuleCat.hom_ext
  apply tensor_ext
  intro a x
  obtain ⟨m, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Affine.ChartSections.iso U hU (K.X i)).hom).surjective x
  exact (PrincipalComplex.chartIso_tmul U hU r (.down ℕ) K i a m).trans
    (AffinePrincipal.Hom.Comparison.chartIso_tmul U hU r (K.X i) a m).symm

theorem sectionComplexIso_square :
    ((PrincipalComplex.tensorFunctor U r).mapHomologicalComplex (.up ℕ)).map
        (Affine.LinearResolutionPurity.sectionComplexIso U hU N K).hom ≫
      (linearIso U hU r N K e).hom =
    (PrincipalComplex.iso U hU r (.up ℕ)
      (Affine.LinearResolutionPurity.internalComplex N K)).hom ≫
        (Affine.LinearResolutionPurity.sectionComplexIso
          (Sections.openSubset U r) (hU.basicOpen r) N K).hom := by
  let : MulAction Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N) :=
    (ModuleCat.isModule _).toDistribMulAction.toMulAction
  let : IsLocalization.Away r Γ(X, Sections.openSubset U r) := hU.isLocalization_basicOpen r
  let : Module.Flat Γ(X, U) Γ(X, Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, Sections.openSubset U r) (Submonoid.powers r)
  let (i : ℕ) : Module.Free Γ(X, U) ((chartComplex U hU K).X i) :=
    inferInstanceAs (Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i)))
  let (i : ℕ) : Module.Finite Γ(X, U) ((chartComplex U hU K).X i) :=
    inferInstanceAs (Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X i)))
  apply Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply tensor_ext
  intro a q
  change Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X i) N, U) at q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (AffinePrincipal.Hom.Comparison.chartIso U hU r (K.X i)).hom).surjective z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw
  | tmul b m =>
      change (LinearHomBaseChange.component Γ(X, U) Γ(X, Sections.openSubset U r)
        (chartComplex U hU K) (chartComplex (Sections.openSubset U r) (hU.basicOpen r) K)
        (PrincipalComplex.chartIso U hU r (.down ℕ) K) _ _ e
        (targetFrame U hU r N e) i (a ⊗ₜ[Γ(X, U)] Affine.HomEvaluation.chartEvaluation (K.X i) N U hU q))
          ((AffinePrincipal.Hom.Comparison.chartIso U hU r (K.X i)).hom
            (b ⊗ₜ[Γ(X, U)] m)) =
        Affine.HomEvaluation.chartEvaluation (K.X i) N (Sections.openSubset U r) (hU.basicOpen r)
          (a • (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X i) N).presheaf.map (Sections.inclusion U r).op q)
          ((AffinePrincipal.Hom.Comparison.chartIso U hU r (K.X i)).hom (b ⊗ₜ[Γ(X, U)] m))
      have hl := LinearHomBaseChange.component_evaluation_literal
        Γ(X, U) Γ(X, Sections.openSubset U r) (chartComplex U hU K)
        (chartComplex (Sections.openSubset U r) (hU.basicOpen r) K)
        (PrincipalComplex.chartIso U hU r (.down ℕ) K) _ _ e
        (AffinePrincipal.Hom.Comparison.chartIso U hU r N) i a b
        (Affine.HomEvaluation.chartEvaluation (K.X i) N U hU q) m
      have hc := ConcreteCategory.congr_hom (chart_component U hU r K i)
        (b ⊗ₜ[Γ(X, U)] m)
      have hl' := (congrArg (fun z =>
        (LinearHomBaseChange.component Γ(X, U) Γ(X, Sections.openSubset U r)
          (chartComplex U hU K) (chartComplex (Sections.openSubset U r) (hU.basicOpen r) K)
          (PrincipalComplex.chartIso U hU r (.down ℕ) K) _ _ e
          (targetFrame U hU r N e) i
          (a ⊗ₜ[Γ(X, U)] Affine.HomEvaluation.chartEvaluation (K.X i) N U hU q)) z) hc).symm.trans hl
      refine hl'.trans ?_
      have hs := (((AffineOpen.LinearHom.comparison (Sections.openSubset U r) (hU.basicOpen r) N).app
        (op (K.X i))).hom).map_smul a
          ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X i) N).presheaf.map (Sections.inclusion U r).op q)
      have hse := ConcreteCategory.congr_hom hs
        ((AffinePrincipal.Hom.Comparison.chartIso U hU r (K.X i)).hom (b ⊗ₜ[Γ(X, U)] m))
      change (AffinePrincipal.Hom.Comparison.chartIso U hU r N).hom
          ((a * b) ⊗ₜ[Γ(X, U)] Affine.HomEvaluation.chartEvaluation (K.X i) N U hU q m) =
        Affine.HomEvaluation.chartEvaluation (K.X i) N (Sections.openSubset U r) (hU.basicOpen r)
          (a • (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X i) N).presheaf.map (Sections.inclusion U r).op q)
          ((AffinePrincipal.Hom.Comparison.chartIso U hU r (K.X i)).hom (b ⊗ₜ[Γ(X, U)] m))
      erw [hse]
      change _ = a • Affine.HomEvaluation.chartEvaluation (K.X i) N (Sections.openSubset U r) (hU.basicOpen r)
        ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (K.X i) N).presheaf.map (Sections.inclusion U r).op q)
        ((AffinePrincipal.Hom.Comparison.chartIso U hU r (K.X i)).hom (b ⊗ₜ[Γ(X, U)] m))
      rw [AffinePrincipal.Hom.Comparison.comparison_tmul, ← map_smul,
        TensorProduct.smul_tmul', smul_eq_mul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.LinearHom
