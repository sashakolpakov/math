import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram
import OAI.Algorithms.SubexponentialSAT.SubexpTruncatedGeometric

namespace OAI.Algorithms

/-! Semantic invariant for the actual fixed-width polynomial Horner fold.
Truncation at every multiplication is valid for the final shifted polynomial. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram
open Polynomial

private theorem nativeFold_eq_foldl {A : Type*} (step : A → A → A)
    (cs : List A) (seed : A) : HornerProgram.fold step cs seed=cs.foldl step seed := by
  induction cs generalizing seed with
  | nil => rfl
  | cons c cs ih => exact ih (step seed c)

/-- Instantiate with the native fixed-length dense polynomial services. The
premises state decoded arithmetic laws, rather than providing a shift oracle. -/
theorem shifted_horner_denote {C A R : Type*} [CommRing R]
    (D : ℕ) (decode : C → R) (denote : A → Polynomial R)
    (lift : C → A) (zero x : A) (theta : R) (mul add : A → A → A)
    (hz : denote zero=0)
    (hx : denote x=Truncation.trunc D (X+Polynomial.C theta))
    (hc : ∀ c, denote (lift c)=Truncation.trunc D (Polynomial.C (decode c)))
    (hm : ∀ a b, denote (mul a b)=Truncation.trunc D (denote a*denote b))
    (ha : ∀ a b, denote (add a b)=denote a+denote b)
    (cs : List C) :
    denote (HornerProgram.fold (HornerProgram.stepValue mul add x)
      (cs.map lift).reverse zero) =
      Truncation.trunc D ((PolynomialAlgorithm.denote (cs.map decode)).comp (X+Polynomial.C theta)) := by
  rw [nativeFold_eq_foldl,List.foldl_reverse]
  induction cs with
  | nil => simp [hz]
  | cons c cs ih =>
      simp only [List.map_cons,List.foldr_cons]
      change denote (add (mul _ x) (lift c)) = _
      rw [ha,hm,ih,hx,hc,SubexpTruncatedGeometric.trunc_mul_trunc,
        ←Truncation.trunc_add]
      congr 1
      simp only [PolynomialAlgorithm.denote,Polynomial.add_comp,Polynomial.mul_comp,
        Polynomial.C_comp,Polynomial.X_comp]
      ring

end SubexponentialSAT.SqrtLog.PerturbationProgram

end OAI.Algorithms
