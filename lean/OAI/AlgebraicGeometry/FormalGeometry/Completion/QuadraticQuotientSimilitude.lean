import OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalQuadraticForm
import OAI.AlgebraicGeometry.FormalGeometry.Completion.QuadraticKernelQuotient

/-! # Quadratic Quotient Similitude -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! A similitude preserves the quadratic kernel and acts as a similitude
on its positive definite rational quotient. -/

open scoped TensorProduct

universe u
variable {G : Type u} [AddCommGroup G] (q : NonnegativeQuadraticMk.Construction.NonnegativeQuadratic G)

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalQuotient_posDef : q.quotientQuadratic.rationalQuadraticForm.PosDef := by
  apply q.quotientQuadratic.rationalQuadraticForm_posDef
  intro g hg
  exact (q.quotientValue_eq_zero_iff g).mp hg

variable (f : G →+ G) (c : ℚ) (hf : ∀ g, q.value (f g) = c * q.value g)

include hf in
theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.map_mem_zeroKernel (g : G) (hg : g ∈ q.zeroKernel) : f g ∈ q.zeroKernel := by
  change q.value (f g) = 0
  rw [hf, hg, mul_zero]

def NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.kernelSimilitude : q.zeroKernel →+ q.zeroKernel :=
  (f.comp q.zeroKernel.subtype).codRestrict q.zeroKernel (fun g => q.map_mem_zeroKernel f c hf g g.property)

def NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.quotientSimilitude : G ⧸ q.zeroKernel →+ G ⧸ q.zeroKernel :=
  QuotientAddGroup.map q.zeroKernel q.zeroKernel f (fun g hg => q.map_mem_zeroKernel f c hf g hg)

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.quotientSimilitude_value (x : G ⧸ q.zeroKernel) :
    q.quotientQuadratic.value (q.quotientSimilitude f c hf x) = c * q.quotientQuadratic.value x := by
  induction x using Quotient.inductionOn with
  | h g => exact hf g

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalQuotientSimilitude (x : TensorProduct ℤ ℚ (G ⧸ q.zeroKernel)) :
    q.quotientQuadratic.rationalQuadraticForm ((q.quotientSimilitude f c hf).toIntLinearMap.baseChange ℚ x) =
      c * q.quotientQuadratic.rationalQuadraticForm x :=
  q.quotientQuadratic.rationalQuadraticForm_similitude (q.quotientSimilitude f c hf) c
    (q.quotientSimilitude_value f c hf) x

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
