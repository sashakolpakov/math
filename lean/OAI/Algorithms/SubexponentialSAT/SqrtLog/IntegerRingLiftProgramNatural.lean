import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update serviceSpec_frame)

def naturalCommand (add : Code) : Code :=
  .seq (copy 249 247) (.seq (copy 250 248) (.seq (scanCommand add) (clear 248)))

def naturalValue {C : Type*} (add : C → C → C) (zero one : C) (bits : List Bool) : C :=
  (scan add bits zero one).1

def naturalBudget (bits K W : ℕ) : ℕ :=
  bits * (2 * (K + 40 * W + 50) + 3) + 16 * W + 15

theorem naturalValue_decode {C A : Type*} [Ring A] (decode : C → A)
    (add : C → C → C) (ha : ∀ x y, decode (add x y) = decode x + decode y)
    (zero one : C) (hz : decode zero = 0) (ho : decode one = 1) (bits : List Bool) :
    decode (naturalValue add zero one bits) = (BinaryArithmetic.toNat bits : A) := by
  simp [naturalValue, scan_decode decode add ha, hz, ho]

theorem naturalCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (add : Code) (op : C → C → C) (K W : ℕ)
    (ha : ServiceSpec base encode add op K) (hw : ∀ a, (encode a).length ≤ W)
    (s : Store) (zero one : C) (hf : LowFrame base s) (hc : Clean s)
    (hz : s 249 = encode zero) (ho : s 250 = encode one)
    (h247 : s 247 = []) (h248 : s 248 = []) :
    ExecutesIn (naturalCommand add) (naturalBudget (s 246).length K W) s
      (Function.update (Function.update s 246 []) 247
        (encode (naturalValue op zero one (s 246)))) := by
  let a := naturalValue op zero one (s 246)
  let p := (scan op (s 246) zero one).2
  let s1 := Function.update s 247 (encode zero)
  let s2 := Function.update s1 248 (encode one)
  let s3 := scanState s2 encode [] a p
  have h1 : ExecutesIn (copy 249 247) (7*W+5) s s1 := by
    have h := copy_run 249 247 s (by decide) (by decide) (by decide) hc.1
    simp only [hz, h247, List.append_nil] at h
    exact h.mono (by have := hw zero; omega)
  have h2 : ExecutesIn (copy 250 248) (7*W+5) s1 s2 := by
    have h := copy_run 250 248 s1 (by decide) (by decide) (by decide)
      (by simp [s1, hc.1])
    have hs : s1 250 = encode one := by simp [s1, ho]
    have he : s1 248 = [] := by simp [s1, h248]
    simp only [hs, he, List.append_nil] at h
    exact h.mono (by have := hw one; omega)
  have hf2 : LowFrame base s2 := lowFrame_update
    (lowFrame_update hf 247 (by decide) _) 248 (by decide) _
  have hc2 : Clean s2 := by simpa [s2, s1, Clean] using hc
  have hi : scanState s2 encode (s 246) zero one = s2 := by
    funext i
    by_cases h246 : i = 246 <;> by_cases h247' : i = 247 <;> by_cases h248' : i = 248 <;>
      simp [scanState, s2, s1, h246, h247', h248']
  have h3 : ExecutesIn (scanCommand add)
      ((s 246).length * (2*(K+40*W+50)+3)+2) s2 s3 := by
    have h := scanCommand_run s2 encode add op K W (serviceSpec_frame ha hf2) hw
      hc2 (s 246) zero one
    rw [hi] at h
    exact h
  have he : Function.update s3 248 [] =
      Function.update (Function.update s 246 []) 247 (encode a) := by
    funext i
    by_cases h246 : i = 246 <;> by_cases h247' : i = 247 <;> by_cases h248' : i = 248 <;>
      simp [s3, scanState, s2, s1, h246, h247', h248', h248]
  have h4 : ExecutesIn (clear 248) (2*W+3) s3
      (Function.update (Function.update s 246 []) 247 (encode a)) := by
    have h := clear_run 248 s3
    rw [he] at h
    exact h.mono (by have := hw p; simp [s3, scanState]; omega)
  have h := h1.seq (h2.seq (h3.seq h4))
  exact h.mono (by unfold naturalBudget; omega)

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
