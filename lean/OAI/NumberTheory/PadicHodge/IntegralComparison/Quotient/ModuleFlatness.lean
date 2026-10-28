import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.BaseChange
import Mathlib.RingTheory.Flat.Basic

/-! # Module Flatness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.ModuleFlatness

noncomputable section

/-! Flatness survives native quotient base change of the original module. -/

open scoped TensorProduct

universe u v

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal R) [Module.Flat R A]

theorem flat : Module.Flat (R ⧸ I) (A ⧸ I.map (algebraMap R A)) := by
  let : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A) := inferInstance
  exact Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.ModuleFlatness
