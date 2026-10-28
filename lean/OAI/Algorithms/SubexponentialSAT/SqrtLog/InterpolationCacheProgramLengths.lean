import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram

namespace OAI.Algorithms

/-! Exact physical output lengths for relocation and cleanup costs. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT SubexpLiftRing

@[simp] theorem inverseBytes_length (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :
    (inverseBytes t a M cache minusOne xs).length=xs.length*(d*baseWidth 3 t) :=
  flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs

@[simp] theorem negativeBytes_length (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :
    (negativeBytes t a M cache minusOne xs).length=xs.length*(d*baseWidth 3 t) :=
  flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs

@[simp] theorem rowBytes_length (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) (x : Coeff t d) :
    (rowBytes t a M cache minusOne xs x).length=xs.length*(d*baseWidth 3 t) :=
  flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs

@[simp] theorem differenceBytes_length (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :
    (differenceBytes t a M cache minusOne xs).length=xs.length*(xs.length*(d*baseWidth 3 t)) :=
  flatMap_length _ _ (rowBytes_length t a M cache minusOne xs) xs

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
