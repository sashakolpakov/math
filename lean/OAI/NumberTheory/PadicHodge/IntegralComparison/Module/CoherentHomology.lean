import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.NoetherianKernels
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Coherent Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CoherentHomology

noncomputable section

/-! The original homology of coherent scheme-module complexes remains coherent. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (S : ShortComplex X.Modules)
  [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]

theorem quasicoherent : S.homology.IsQuasicoherent := by
  let : (kernel S.g).IsQuasicoherent := Independent.QuasicoherentKernels.quasicoherent S.g
  let f := kernel.lift S.g S.f S.zero
  have hc : (cokernel f).IsQuasicoherent := Independent.QuasicoherentCokernels.quasicoherent f
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso S.homologyIsoCokernelLift.symm hc

theorem finiteType [IsLocallyNoetherian X] [S.X₂.IsFiniteType] : S.homology.IsFiniteType := by
  let : (kernel S.g).IsQuasicoherent := Independent.QuasicoherentKernels.quasicoherent S.g
  let : (kernel S.g).IsFiniteType := Independent.NoetherianKernels.finiteType S.g
  let f := kernel.lift S.g S.f S.zero
  let : (cokernel f).IsQuasicoherent := Independent.QuasicoherentCokernels.quasicoherent f
  have hf : (cokernel f).IsFiniteType := FiniteTypeQuotient.of_epi (cokernel.π f)
  exact @FiniteTypeIso.finiteType X (cokernel f) S.homology S.homologyIsoCokernelLift.symm hf

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CoherentHomology
