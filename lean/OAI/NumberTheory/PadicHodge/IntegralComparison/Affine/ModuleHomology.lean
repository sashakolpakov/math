import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleExactSections
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Module Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleHomology

noncomputable section

/-! The canonical affine-sections comparison preserves actual quasicoherent homology. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleExactSections

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (S : ShortComplex X.Modules)
  [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]

include hU

theorem preservesLeft : (ModuleExactSections.sections U).PreservesLeftHomologyOf S := by
  let : (kernel S.g).IsQuasicoherent := Independent.QuasicoherentKernels.quasicoherent S.g
  let h := ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S
  have : h.IsPreservedBy (ModuleExactSections.sections U) :=
    { g := inferInstance
      f' := ModuleExactSections.preservesCokernel U hU (kernel.lift S.g S.f S.zero) }
  exact Functor.PreservesLeftHomologyOf.mk' (ModuleExactSections.sections U) h

omit [S.X₃.IsQuasicoherent] in
theorem preservesRight : (ModuleExactSections.sections U).PreservesRightHomologyOf S := by
  let h := ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel S
  have : h.IsPreservedBy (ModuleExactSections.sections U) :=
    { f := ModuleExactSections.preservesCokernel U hU S.f
      g' := inferInstance }
  exact Functor.PreservesRightHomologyOf.mk' (ModuleExactSections.sections U) h

def iso : (S.map (ModuleExactSections.sections U)).homology ≅ (ModuleExactSections.sections U).obj S.homology := by
  have := preservesLeft U hU S
  exact S.mapHomologyIso (ModuleExactSections.sections U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleHomology
