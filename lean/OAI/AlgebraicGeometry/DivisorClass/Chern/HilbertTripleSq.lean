import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Hilbert Triple Sq -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HilbertTripleSq

noncomputable section

/-! The Hilbert product used for a form, its Dolbeault derivative, and its adjoint derivative. -/

variable (A B C : Type*) [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup C] [InnerProductSpace ℂ C]

abbrev HilbertTriple := WithLp 2 (A × WithLp 2 (B × C))

def hilbertTripleCoordinates : HilbertTriple A B C ≃L[ℂ] A × (B × C) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ A (WithLp 2 (B × C))).trans
    ((ContinuousLinearEquiv.refl ℂ A).prodCongr (WithLp.prodContinuousLinearEquiv 2 ℂ B C))

def hilbertTripleFirst : HilbertTriple A B C →L[ℂ] A :=
  (ContinuousLinearMap.fst ℂ A (B × C)).comp (hilbertTripleCoordinates A B C).toContinuousLinearMap

def hilbertTripleSecond : HilbertTriple A B C →L[ℂ] B :=
  (ContinuousLinearMap.fst ℂ B C).comp
    ((ContinuousLinearMap.snd ℂ A (B × C)).comp (hilbertTripleCoordinates A B C).toContinuousLinearMap)

def hilbertTripleThird : HilbertTriple A B C →L[ℂ] C :=
  (ContinuousLinearMap.snd ℂ B C).comp
    ((ContinuousLinearMap.snd ℂ A (B × C)).comp (hilbertTripleCoordinates A B C).toContinuousLinearMap)

theorem hilbertTriple_inner (z w : HilbertTriple A B C) :
    inner ℂ z w =
      inner ℂ (hilbertTripleFirst A B C z) (hilbertTripleFirst A B C w) +
      inner ℂ (hilbertTripleSecond A B C z) (hilbertTripleSecond A B C w) +
      inner ℂ (hilbertTripleThird A B C z) (hilbertTripleThird A B C w) := by
  change inner ℂ z w = inner ℂ z.fst w.fst + inner ℂ z.snd.fst w.snd.fst + inner ℂ z.snd.snd w.snd.snd
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, add_assoc]
  rfl

theorem hilbertTriple_norm_sq (z : HilbertTriple A B C) :
    ‖z‖ ^ 2 = ‖hilbertTripleFirst A B C z‖ ^ 2 +
      ‖hilbertTripleSecond A B C z‖ ^ 2 + ‖hilbertTripleThird A B C z‖ ^ 2 := by
  change ‖z‖ ^ 2 = ‖z.fst‖ ^ 2 + ‖z.snd.fst‖ ^ 2 + ‖z.snd.snd‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, add_assoc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HilbertTripleSq
