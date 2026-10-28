import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleHomology
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.Functor

/-! # Module Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleHomology

noncomputable section

/-! The whole native principal-open section presheaf preserves the
homology of quasicoherent complexes, with its actual restriction maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleFunctor
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

theorem preservesKernel {M N : X.Modules} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (ModuleFunctor.functor U hU) := by
  apply preservesLimit_of_evaluation
  intro r
  change PreservesLimit (parallelPair f 0)
    (Affine.ModuleExactSections.sections (SectionPresheaf.openSubset U r.unop) ⋙
      ModuleCat.restrictScalars (algebraMap Γ(X, U) Γ(X, SectionPresheaf.openSubset U r.unop)))
  infer_instance

theorem preservesCokernel {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) : PreservesColimit (parallelPair f 0) (ModuleFunctor.functor U hU) := by
  apply preservesColimit_of_evaluation
  intro r
  let := Affine.ModuleExactSections.preservesCokernel
    (SectionPresheaf.openSubset U r.unop) (hU.basicOpen r.unop.val) f
  change PreservesColimit (parallelPair f 0)
    (Affine.ModuleExactSections.sections (SectionPresheaf.openSubset U r.unop) ⋙
      ModuleCat.restrictScalars (algebraMap Γ(X, U) Γ(X, SectionPresheaf.openSubset U r.unop)))
  infer_instance

variable (S : ShortComplex X.Modules)
  [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]

theorem preservesLeft : (ModuleFunctor.functor U hU).PreservesLeftHomologyOf S := by
  let : (kernel S.g).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel S.g
  let h := ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S
  let : h.IsPreservedBy (ModuleFunctor.functor U hU) :=
    { g := preservesKernel U hU S.g
      f' := preservesCokernel U hU (kernel.lift S.g S.f S.zero) }
  exact Functor.PreservesLeftHomologyOf.mk' (ModuleFunctor.functor U hU) h

def iso : (S.map (ModuleFunctor.functor U hU)).homology ≅ (ModuleFunctor.functor U hU).obj S.homology := by
  letI := preservesLeft U hU S
  exact S.mapHomologyIso (ModuleFunctor.functor U hU)

omit [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] in
def complexIso (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent] (q : ℕ) :
    (((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).obj K).homology q ≅
      (ModuleFunctor.functor U hU).obj (K.homology q) := by
  letI : (K.sc q).X₁.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).prev q)).IsQuasicoherent
  letI : (K.sc q).X₂.IsQuasicoherent := inferInstanceAs (K.X q).IsQuasicoherent
  letI : (K.sc q).X₃.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).next q)).IsQuasicoherent
  exact iso U hU (K.sc q)

omit [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] in
theorem exactAt (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
    (q : ℕ) (hK : K.ExactAt q) :
    (((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).obj K).ExactAt q := by
  apply (exactAt_iff_isZero_homology _ _).mpr
  exact ((ModuleFunctor.functor U hU).map_isZero ((exactAt_iff_isZero_homology _ _).mp hK)).of_iso
    (complexIso U hU K q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleHomology
