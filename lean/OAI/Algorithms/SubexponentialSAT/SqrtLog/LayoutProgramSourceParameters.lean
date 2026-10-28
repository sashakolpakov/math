import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceConfiguration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeInputs
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

namespace OAI.Algorithms

/-! Pure packaging of the caches produced by native setup. No execution,
source polynomial, or interpolation table is supplied by this constructor.
The integer encoder below is a semantic witness used in the row proof; the
runtime integer lift remains the already checked native program. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open IntegerRingLiftProgram RowSelectionProgram

namespace Parameters

/-- Coefficientwise representation of a ring element, for semantic proofs. -/
def represent (t : ℕ) (ht : 0 < t) {d : ℕ} (model : RingModel.Data d)
    (x : model.O t) : ModelCode t d :=
  fun i => encodeWord 3 t (model.coordinates t ht x i)

theorem represent_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (x : model.O t) :
    (RingProgram.modelRing t ht hd model M cache).decode (represent t ht model x)=x := by
  rw [RingProgram.modelRing_decode]
  simp only [represent,wordValue_encodeWord]
  exact (model.coordinates t ht).symm_apply_apply x

/-- The inverse word produced by the native denominator loop determines the
unit used by the mathematical row construction. -/
def denominatorUnit (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (R : ℕ) (inv : ModelCode t d)
    (hinv : (RingProgram.modelRing t ht hd model M cache).decode inv *
      (2 : model.O t)^(R-1)=1) : (model.O t)ˣ where
  val := (LayoutNumerator.denominator R : model.O t)
  inv := (RingProgram.modelRing t ht hd model M cache).decode inv
  val_inv := by simpa [LayoutNumerator.denominator,mul_comm] using hinv
  inv_val := by simpa [LayoutNumerator.denominator] using hinv

/-- Only the actual head-input record, generated H-cache invariant, typed ring
caches, and generated inverse equation are needed to form source parameters. -/
def ofInputs (s : LeafHeadSetupProgram.Native.Inputs)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height
      (LeafHeadSetupProgram.unary s.R) s.width words)
    (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (minusOne inv : ModelCode t d)
    (hm : (RingProgram.modelRing t ht hd model M cache).decode minusOne = -1)
    (hi : (RingProgram.modelRing t ht hd model M cache).decode inv *
      (2 : model.O t)^(s.R-1)=1)
    (hfield : s.Q < 3^d) : Parameters s.r s.Q d where
  t := t
  ht := ht
  hd := hd
  model := model
  modulus := M
  cache := cache
  hz := hz
  R := s.R
  hwords := words
  width := s.width
  power := s.power
  aWord := s.height
  hlen := by simpa [LeafHeadSetupProgram.unary] using hc.1
  hwidths := hc.2.1
  hvalues := by simpa [LeafHeadSetupProgram.unary] using hc.2.2
  hp := s.power_signed
  hpt := s.power_total
  hwidth := s.width_node
  hAQ := s.height_le
  hQ := by have h := s.node.isLt; omega
  hfield := hfield
  minusOne := minusOne
  hminus := hm
  invDenom := inv
  denom := denominatorUnit t ht hd model M cache s.R inv hi
  hdenom := rfl
  hinv := rfl
  integerWord := fun z => represent t ht model (z : model.O t)
  hinteger := fun z => represent_decode t ht hd model M cache (z : model.O t)
  ringWidth := List.replicate (d*baseWidth 3 t) true
  rowWidth := List.replicate (s.Q*(d*baseWidth 3 t)) true
  hringWidth := List.length_replicate
  hrowWidth := by simp only [List.length_replicate]

/-- The actual produced ring, its canonical scalar cache, and its generated
half determine every ring-valued field of `Parameters`. The inverse word is
exactly the value written by `LayoutDenominatorProgramQuery` to port728. -/
def ofProduced (s : LeafHeadSetupProgram.Native.Inputs)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height
      (LeafHeadSetupProgram.unary s.R) s.width words)
    (m : LeafParametersProgram.Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (u : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache u e)
    (hfield : s.Q < 3^(m.val 34)) : Parameters s.r s.Q (m.val 34) :=
  ofInputs s words hc (m.val 33) ht hd (IrreducibleSearch.data hd) M cache hp.caches.canonical
    (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
    (LayoutDenominatorProgramQuery.value (m.val 33) (IrreducibleSearch.data hd) M cache u s.R)
    (LeafProgram.Constants.minusOne_decode _ ht hd _ M cache)
    (LayoutDenominatorProgram.value_inverse _ ht hd _ M cache _ _ _
      (LeafProgram.Constants.zero_decode _ ht hd _ M cache)
      (LeafProgram.Constants.one_decode _ ht hd _ M cache)
      (LeafProgram.Constants.minusOne_decode _ ht hd _ M cache) u hp.caches.inverse s.R)
    hfield

end Parameters
end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end

end OAI.Algorithms
