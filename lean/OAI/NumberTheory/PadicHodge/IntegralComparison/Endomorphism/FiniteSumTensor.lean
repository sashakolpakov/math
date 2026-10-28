import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumPicard
import OAI.NumberTheory.PadicHodge.IntegralComparison.PicardTensorAction

/-! # Finite Sum Tensor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumTensor

noncomputable section

/-! The actual coherent K-theory action of finite endomorphism sums is
an ordered orbit of fixed tensor operators with quadratic exponents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumPicard OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.EulerPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.PicardTensorAction OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyNewton.Family

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  {ι : Type v} [Fintype ι]

def factor (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    (t : Fin (Fintype.card (ι × ι))) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left :=
  FiniteSumPicard.crossBundle A L (f ((Fintype.equivFin (ι × ι)).symm t).1)
    (f ((Fintype.equivFin (ι × ι)).symm t).2)

def weight (a : ι → ℕ) (t : Fin (Fintype.card (ι × ι))) : ℕ :=
  2 * (a ((Fintype.equivFin (ι × ι)).symm t).1 * a ((Fintype.equivFin (ι × ι)).symm t).2)

theorem pullback_class (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (a : ι → ℕ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (2 • ∑ i, a i • f i).toMul.hom.hom.left) =
      ∏ t, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (factor A L f t) ^ weight a t := by
  rw [FiniteSumPicard.double_sum_pullback_class A L hsym f a]
  calc
    _ = ∏ t : ι × ι, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (FiniteSumPicard.crossBundle A L (f t.1) (f t.2)) ^
        (2 * (a t.1 * a t.2)) :=
      (Fintype.prod_prod_type (fun t : ι × ι =>
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (FiniteSumPicard.crossBundle A L (f t.1) (f t.2)) ^ (2 * (a t.1 * a t.2)))).symm
    _ = _ := Fintype.prod_equiv (Fintype.equivFin (ι × ι)) _ _
      (fun t => by simp only [factor, weight, Equiv.symm_apply_apply])

theorem tensorEnd_double_sum_power (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (a : ι → ℕ) (m : ℕ) :
    EulerPolynomial.tensorEnd (L.pullback (2 • ∑ i, a i • f i).toMul.hom.hom.left) ^ m =
      Finite.FamilyNewton.Family.ordered (fun t => EulerPolynomial.tensorEnd (factor A L f t)) (fun t => weight a t * m) := by
  have hc : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (2 • ∑ i, a i • f i).toMul.hom.hom.left) ^ m =
      ∏ t, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (factor A L f t) ^ (weight a t * m) := by
    rw [pullback_class A L hsym f a, ← Finset.prod_pow]
    simp only [pow_mul]
  calc
    _ = PicardTensorAction.action A.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf
        (L.pullback (2 • ∑ i, a i • f i).toMul.hom.hom.left) ^ m) := by
      rw [map_pow, PicardTensorAction.action_class]
    _ = PicardTensorAction.action A.left (∏ t, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (factor A L f t) ^ (weight a t * m)) :=
      congrArg (PicardTensorAction.action A.left) hc
    _ = _ := PicardTensorAction.action_prod_pow A.left (factor A L f) (fun t => weight a t * m)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumTensor
