import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.EulerPolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyNewton

/-! # Picard Tensor Action -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PicardTensorAction

noncomputable section

/-! The actual Picard group acts on coherent K-theory by tensoring.
Finite products are evaluated in the specified order. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.EulerPolynomial OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyNewton.Family

universe u

variable (X : Scheme.{u})

def action : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X →* AddMonoid.End (Coherent.KTheory.Projective.CoherentK0 X) where
  toFun := Quotient.lift Endomorphism.EulerPolynomial.tensorEnd (fun _ _ ⟨e⟩ => Coherent.KTheory.Projective.coherentTensorK0_congr _ _ e)
  map_one' := Coherent.KTheory.Projective.coherentTensorK0_unit X
  map_mul' c d := by
    refine Quotient.inductionOn₂ c d (fun L M => ?_)
    exact Endomorphism.EulerPolynomial.tensorEnd_tensor L M

theorem action_class (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) : action X (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = Endomorphism.EulerPolynomial.tensorEnd L := rfl

theorem action_prod_pow {r : ℕ} (L : Fin r → AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (a : Fin r → ℕ) :
    action X (∏ i, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L i) ^ a i) = Finite.FamilyNewton.Family.ordered (fun i => Endomorphism.EulerPolynomial.tensorEnd (L i)) a := by
  induction r with
  | zero => simp [Finite.FamilyNewton.Family.ordered]
  | succ r ih =>
    rw [Fin.prod_univ_succ, map_mul, map_pow, action_class, ih]
    rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PicardTensorAction
