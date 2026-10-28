import OAI.AlgebraicTopology.DeRham.Comparison.ConvexResolution
import OAI.Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence
import OAI.Analysis.DifferentialForms.Manifold.OpenDeRham
import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant

/-! # Convex Manifold Resolution -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ConvexManifoldResolution

noncomputable section

/-!
# The actual locally constant resolution in the local manifold-form model

On an open subset of a normed space, the proved identification of coefficient
forms with ambient local manifold forms is an isomorphism of de Rham complexes.
It transports the actual locally constant augmentation, and its degree-zero
component is proved to be the standard locally constant manifold zero-form.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual local coefficient and manifold form models define isomorphic complexes. -/
def localNormedDeRhamIso (U : Opens E) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex E U ≅ Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv U n).toModuleIso) (by
      intro i j hij
      obtain rfl := (show i + 1 = j from hij)
      rw [Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex_d, Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro form
      exact Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv_d form)

@[simp]
theorem localNormedDeRhamIso_hom_f_apply (U : Opens E) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    (localNormedDeRhamIso U).hom.f n form = Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv U n form := rfl

@[simp]
theorem localNormedDeRhamIso_inv_f_apply (U : Opens E) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) :
    (localNormedDeRhamIso U).inv.f n form = (Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv U n).symm form := rfl

/-- These concrete complex identifications respect actual open restriction. -/
theorem localNormedDeRhamIso_restrict {U V : Opens E} (hVU : V ≤ U) :
    Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamRestrict E hVU ≫ (localNormedDeRhamIso V).hom =
      (localNormedDeRhamIso U).hom ≫ Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamRestrict hVU := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv_restrict hVU form

/-- The genuine locally constant zero-form is preserved by coefficient coordinates. -/
theorem localNormedFormEquiv_locallyConstant (U : Opens E) (f : LocallyConstant U ℂ) :
    Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv U 0 (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U f) =
      LocallyConstantZeroForms.locallyConstantToZeroForm U f := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rw [Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv_apply]
  apply ContinuousAlternatingMap.ext
  intro v
  exact (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_apply U f x _).trans
    (LocallyConstantZeroForms.locallyConstantToZeroForm_apply U f x v).symm

theorem localNormedFormEquiv_symm_locallyConstant (U : Opens E) (f : LocallyConstant U ℂ) :
    (Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv U 0).symm (LocallyConstantZeroForms.locallyConstantToZeroForm U f) =
      Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U f := by
  apply (Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv U 0).injective
  rw [LinearEquiv.apply_symm_apply, localNormedFormEquiv_locallyConstant]

/-- The actual locally constant augmentation, transported to local manifold forms. -/
def locallyConstantOpenManifoldDeRhamResolutionMap (U : Opens E) :
    (CochainComplex.single₀ (ModuleCat.{0} ℂ)).obj
      (ModuleCat.of ℂ (LocallyConstant U ℂ)) ⟶ Analysis.DifferentialForms.Manifold.OpenDeRham.openManifoldDeRhamComplex E U :=
  ConvexResolution.locallyConstantOpenDeRhamResolutionMap U ≫ (localNormedDeRhamIso U).inv

/-- The transported augmentation is literally the standard local manifold zero-form inclusion. -/
@[simp]
theorem locallyConstantOpenManifoldDeRhamResolutionMap_f_zero (U : Opens E) :
    (locallyConstantOpenManifoldDeRhamResolutionMap U).f 0 =
      ModuleCat.ofHom (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U) := by
  rw [locallyConstantOpenManifoldDeRhamResolutionMap, HomologicalComplex.comp_f,
    ConvexResolution.locallyConstantOpenDeRhamResolutionMap_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact localNormedFormEquiv_symm_locallyConstant U f

/-- The actual local manifold-form augmentation is a quasi-isomorphism on every
convex open, including the empty one. -/
theorem locallyConstantOpenManifoldDeRhamResolutionMap_quasiIso_convex
    [FiniteDimensional ℝ E] (U : Opens E) (hU : Convex ℝ (U : Set E)) :
    QuasiIso (locallyConstantOpenManifoldDeRhamResolutionMap U) := by
  let := ConvexResolution.locallyConstantOpenDeRhamResolutionMap_quasiIso_convex U hU
  change QuasiIso (ConvexResolution.locallyConstantOpenDeRhamResolutionMap U ≫ (localNormedDeRhamIso U).inv)
  infer_instance

end

end OAI.AlgebraicTopology.DeRham.Comparison.ConvexManifoldResolution
