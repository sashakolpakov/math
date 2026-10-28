import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsJets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsPerturbation

namespace OAI.Algorithms

/-! Polynomial naturality for the actual H-adic indicator expression. U
remains formal throughout; only its final retained coefficient sum is read. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R] {V : Type*} [DecidableEq V]

/-- Same finite expression as the code-derived assignment indicator. -/
def indicatorJet (t : ℕ) (digits : Fin t → R[X])
    (H : Squarefree.Jet V R) : Squarefree.Jet V R :=
  ∑ s : Fin t, Polynomial.X^s.val *
    (digits s).eval₂ Moments.ringScalar H * IdempotentProgram.hValue H^s.val

theorem jetEval_ringScalar (x : V → R) (hx : ∀ v, x v*x v=x v) (c : R) :
    Moments.jetEval x hx (Moments.ringScalar c) = Polynomial.C (Polynomial.C c) := by
  simp [Moments.jetEval,Moments.ringScalar,Squarefree.weight]

theorem polynomial_eval₂_C (P L : R[X]) :
    P.eval₂ (Polynomial.C.comp Polynomial.C) (Polynomial.C L) =
      Polynomial.C (P.comp L) := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp only [Polynomial.eval₂_add,Polynomial.add_comp,hp,hq,map_add]
  | monomial n c => simp [Polynomial.eval₂_monomial,Polynomial.monomial_comp]

theorem row_eq_fin (t : ℕ) (digits : Fin t → R[X]) (L : R[X]) :
    TotalOrder.row t (digitAt digits L) (IdempotentProgram.hValue L) =
      ∑ s : Fin t, Polynomial.monomial s.val
        ((digits s).comp L * IdempotentProgram.hValue L^s.val) := by
  unfold TotalOrder.row
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [digitAt,dite_eq_left (Fin.isLt _)]

theorem indicatorJet_eval (t : ℕ) (digits : Fin t → R[X])
    (H : Squarefree.Jet V R) (x : V → R) (hx : ∀ v, x v*x v=x v)
    (L : R[X]) (hH : Moments.jetEval x hx H=Polynomial.C L) :
    Moments.jetEval x hx (indicatorJet t digits H) =
      TotalOrder.row t (digitAt digits L) (IdempotentProgram.hValue L) := by
  unfold indicatorJet
  rw [map_sum,row_eq_fin]
  apply Finset.sum_congr rfl
  intro s _
  have hs : (Moments.jetEval x hx).comp Moments.ringScalar =
      Polynomial.C.comp Polynomial.C := by
    exact RingHom.ext (fun c => jetEval_ringScalar x hx c)
  have he := Polynomial.hom_eval₂ (digits s) Moments.ringScalar (Moments.jetEval x hx) H
  rw [hs,hH,polynomial_eval₂_C] at he
  rw [map_mul,map_mul,map_pow,map_pow,he]
  have hu : Moments.jetEval x hx (Polynomial.X : Squarefree.Jet V R) = Polynomial.X := by
    simp [Moments.jetEval]
  have hh : Moments.jetEval x hx (IdempotentProgram.hValue H) =
      Polynomial.C (IdempotentProgram.hValue L) := by
    simp only [IdempotentProgram.hValue,map_mul,map_sub,map_one,map_ofNat,hH]
  rw [hu,hh,← map_pow]
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
  ring

/-- An actual canonical product has the same retained evaluated readout as
its full expression; discarded terms are never interpreted as a ring map. -/
theorem canonical_product_readout (u J : ℕ) (F : Squarefree.Jet V R)
    (x : V → R) (hx : ∀ v, x v*x v=x v) (P : Polynomial R[X])
    (hF : Moments.jetEval x hx F=P) :
    Truncation.trunc J (Moments.sumUCoeff u
      (Moments.jetEval x hx (Squarefree.canonical u J F))) =
      Truncation.trunc J (Moments.sumUCoeff u P) := by
  rw [Moments.evaluated_readout_canonical,hF]

/-- The per-assignment bridge only needs source row identities. -/
theorem product_indicator_readout {I : Type*} [Fintype I]
    (u J : ℕ) (digits : Fin u → R[X]) (F : I → Squarefree.Jet V R)
    (mark : Squarefree.Jet V R) (L : I → R[X]) (m : R[X])
    (x : V → R) (hx : ∀ v, x v*x v=x v)
    (hF : ∀ i, Moments.jetEval x hx (F i)=Polynomial.C (L i))
    (hm : Moments.jetEval x hx mark=Polynomial.C m) :
    Truncation.trunc J (Moments.sumUCoeff u (Moments.jetEval x hx
      (Squarefree.canonical u J ((∏ i, indicatorJet u digits (F i))*mark)))) =
    Truncation.trunc J (TotalOrder.output Finset.univ u
      (fun i => digitAt digits (L i)) (fun i => IdempotentProgram.hValue (L i))*m) := by
  rw [Moments.evaluated_readout_canonical,map_mul,map_prod,hm]
  simp_rw [indicatorJet_eval u digits _ x hx _ (hF _)]
  change Truncation.trunc J (Moments.sumUCoeff u
    (TotalOrder.fullProduct Finset.univ u
      (fun i => digitAt digits (L i)) (fun i => IdempotentProgram.hValue (L i))*Polynomial.C m)) = _
  congr 1
  rw [TotalOrder.output_eq_sum_coeff,Finset.sum_mul]
  simp only [Moments.sumUCoeff,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Polynomial.coeff_mul_C]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
