import OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantResolution
import OAI.AlgebraicTopology.DeRham.Comparison.StarConvex
import OAI.Analysis.DifferentialForms.Manifold.CochainAugmentation

/-! # Convex Resolution -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ConvexResolution

noncomputable section

/-!
# The actual locally constant resolution on convex open domains

Locally constant complex-valued functions map to their actual smooth
zero-forms. The proved kernel identification and all-degree Poincare lemma
make this augmentation a quasi-isomorphism on every convex open domain,
including the empty one. No cohomological comparison is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual locally constant inclusion in the zero term of the open
de Rham complex. -/
def locallyConstantOpenDeRhamZero (U : Opens E) :
    ModuleCat.of ℂ (LocallyConstant U ℂ) ⟶ (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U).X 0 :=
  ModuleCat.ofHom (LocallyConstantZeroForms.locallyConstantToZeroForm U)

/-- Locally constant functions have zero exterior derivative. -/
theorem locallyConstantOpenDeRhamZero_d (U : Opens E) :
    locallyConstantOpenDeRhamZero U ≫ (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U).d 0 1 = 0 := by
  rw [Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact LocallyConstantZeroForms.d_locallyConstantToZeroForm U f

/-- The actual zero-form inclusion is the categorical kernel of the
exterior derivative, on any open domain. -/
def locallyConstantOpenDeRhamZero_isKernel (U : Opens E) :
    IsLimit (KernelFork.ofι (locallyConstantOpenDeRhamZero U)
      (locallyConstantOpenDeRhamZero_d U)) := by
  apply ModuleCat.isLimitKernelFork (locallyConstantOpenDeRhamZero U)
    ((Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U).d 0 1)
  · rw [Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex_d]
    change Function.Exact (LocallyConstantZeroForms.locallyConstantToZeroForm U)
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1)
    rw [LinearMap.exact_iff]
    exact (LocallyConstantZeroForms.range_locallyConstantToZeroForm U).symm
  · exact LocallyConstantZeroForms.locallyConstantToZeroForm_injective U

/-- The genuine locally constant augmentation of the open de Rham complex. -/
def locallyConstantOpenDeRhamResolutionMap (U : Opens E) :
    (CochainComplex.single₀ (ModuleCat.{u} ℂ)).obj
        (ModuleCat.of ℂ (LocallyConstant U ℂ)) ⟶ Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U :=
  (CochainComplex.fromSingle₀Equiv (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U)
    (ModuleCat.of ℂ (LocallyConstant U ℂ))).symm
      ⟨locallyConstantOpenDeRhamZero U, locallyConstantOpenDeRhamZero_d U⟩

@[simp]
theorem locallyConstantOpenDeRhamResolutionMap_f_zero (U : Opens E) :
    (locallyConstantOpenDeRhamResolutionMap U).f 0 = locallyConstantOpenDeRhamZero U :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The actual augmentation commutes with restriction to a smaller open set. -/
theorem locallyConstantOpenDeRhamResolutionMap_restrict {U V : Opens E} (h : V ≤ U) :
    (CochainComplex.single₀ (ModuleCat.{u} ℂ)).map
        (ModuleCat.ofHom (LocallyConstantZeroForms.locallyConstantRestrict h)) ≫
      locallyConstantOpenDeRhamResolutionMap V =
    locallyConstantOpenDeRhamResolutionMap U ≫ Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamRestrict h := by
  apply (CochainComplex.fromSingle₀Equiv (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex V)
    (ModuleCat.of ℂ (LocallyConstant U ℂ))).injective
  apply Subtype.ext
  change ((CochainComplex.single₀ (ModuleCat.{u} ℂ)).map
      (ModuleCat.ofHom (LocallyConstantZeroForms.locallyConstantRestrict h))).f 0 ≫
      (locallyConstantOpenDeRhamResolutionMap V).f 0 =
    (locallyConstantOpenDeRhamResolutionMap U).f 0 ≫ (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamRestrict h).f 0
  rw [CochainComplex.single₀_map_f_zero,
    locallyConstantOpenDeRhamResolutionMap_f_zero,
    locallyConstantOpenDeRhamResolutionMap_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact (LocallyConstantZeroForms.restrict_locallyConstantToZeroForm h f).symm

/-- Poincare's proved all-degree primitive theorem makes the actual locally
constant augmentation a quasi-isomorphism on an open convex domain. -/
theorem locallyConstantOpenDeRhamResolutionMap_quasiIso_convex
    [FiniteDimensional ℝ E] (U : Opens E) (hU : Convex ℝ (U : Set E)) :
    QuasiIso (locallyConstantOpenDeRhamResolutionMap U) :=
  Analysis.DifferentialForms.Manifold.CochainAugmentation.cochainAugmentation_quasiIso (Analysis.DifferentialForms.Manifold.OpenDeRhamX.openDeRhamComplex U)
    (locallyConstantOpenDeRhamZero U) (locallyConstantOpenDeRhamZero_d U)
    (locallyConstantOpenDeRhamZero_isKernel U)
    (fun n => StarConvex.openDeRhamComplex_exactAt_convex hU n)

end

end OAI.AlgebraicTopology.DeRham.Comparison.ConvexResolution
