import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModelNodes
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceTyped

namespace OAI.Algorithms

/-! The native interpolation-cache values implement the exact node units used
by the universal source semantics. No field inverse is assumed in O. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache

open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open InterpolationCacheProgram

variable {d Q : ℕ}

def native (t : ℕ) (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (minusOne : Coeff t d) : NodeCache (Coeff t d) Q where
  node i := RingNodeProgram.nodeCode t d (i.val+1)
  inverse i := inverseValue t a M cache minusOne (RingNodeProgram.nodeCode t d (i.val+1))
  difference i j := differenceValue t a M cache minusOne
    (RingNodeProgram.nodeCode t d (i.val+1)) (RingNodeProgram.nodeCode t d (j.val+1))

private theorem inverse_unique {O : Type*} [CommRing O] {a x y : O}
    (hx : x*a=1) (hy : y*a=1) : x=y := by
  calc
    x=x*(a*y) := by rw [mul_comm a y,hy,mul_one]
    _=(x*a)*y := by ring
    _=y := by rw [hx,one_mul]

theorem native_node (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (hQ : Q < 3^d) (i : Fin Q) :
    (RingProgram.modelRing t ht hd a M cache).decode ((native t a M cache minusOne).node i)=
      a.node t Q ht hQ i :=
  RingNodeProgram.nodeCode_decode t ht hd a M cache Q hQ i

theorem native_inverse (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (hQ : Q < 3^d) (i : Fin Q) :
    (RingProgram.modelRing t ht hd a M cache).decode ((native t a M cache minusOne).inverse i)=
      (a.nodeUnits t Q ht hQ).nodeInverse i := by
  apply inverse_unique (a:=a.node t Q ht hQ i)
  · exact node_inverse_correct t ht hd a M cache minusOne hm Q hQ i
  · exact NodeUnits.nodeInverse_mul _ i

theorem native_difference (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (hQ : Q < 3^d) (i j : Fin Q) :
    (RingProgram.modelRing t ht hd a M cache).decode ((native t a M cache minusOne).difference i j)=
      (a.nodeUnits t Q ht hQ).differenceInverse i j := by
  by_cases hij : i=j
  · subst j
    rw [NodeUnits.differenceInverse,dite_eq_right (by simp)]
    exact differenceValue_diagonal t ht hd a M cache minusOne _ hm
  · apply inverse_unique (a:=a.node t Q ht hQ i-a.node t Q ht hQ j)
    · exact nodes_difference_correct t ht hd a M cache minusOne hm Q hQ i j hij
    · exact NodeUnits.differenceInverse_mul _ hij

theorem native_negative (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (i : Fin Q) :
    (RingProgram.modelRing t ht hd a M cache).decode
      (negativeValue t a M cache minusOne ((native t a M cache minusOne).node i))=
    (RingProgram.modelRing t ht hd a M cache).decode
      (((RingProgram.modelRing t ht hd a M cache).negRun ((native t a M cache minusOne).node i)).1) := by
  rw [(RingProgram.modelRing t ht hd a M cache).neg_correct]
  exact negativeValue_decode t ht hd a M cache minusOne _ hm

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache

end OAI.Algorithms
