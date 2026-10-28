import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramInverseComplete

namespace OAI.Algorithms

/-! Framed native binary calls at arbitrary persistent ports. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

def callAt (code : Code) (left right dst : Fin 256) : Code :=
  .seq (replace left 240) (.seq (replace right 241)
    (.seq code (.seq (SubexpLocalCRTSetup.clearMany [240,241])
      (.seq (replace 244 dst) (clear 244)))))

def CachePort (i : Fin 256) : Prop :=
  205 ≤ i.val ∧ i ≠ 240 ∧ i ≠ 241 ∧ i ≠ 244 ∧ i ≠ 245

instance (i : Fin 256) : Decidable (CachePort i) := by
  unfold CachePort
  infer_instance

theorem callAt_run {C : Type*} (base : Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K W : ℕ)
    (hspec : ServiceSpec base encode code op K)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (a b : C) (left right dst : Fin 256)
    (hl : CachePort left) (hr : CachePort right) (hd : CachePort dst)
    (hf : LowFrame base s) (ha : s left = encode a) (hb : s right = encode b)
    (h120 : s 120 = []) (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (hdlen : (s dst).length ≤ W) :
    ExecutesIn (callAt code left right dst) (K+40*W+50) s
      (Function.update s dst (encode (op a b))) := by
  rcases hl with ⟨hlow, hl240, hl241, hl244, hl245⟩
  rcases hr with ⟨hrow, hr240, hr241, hr244, hr245⟩
  rcases hd with ⟨hdow, hd240, hd241, hd244, hd245⟩
  have hl120 : left ≠ 120 := by intro h; subst left; norm_num [Fin.coe_ofNat_eq_mod] at hlow
  have hr120 : right ≠ 120 := by intro h; subst right; norm_num [Fin.coe_ofNat_eq_mod] at hrow
  have hd120 : dst ≠ 120 := by intro h; subst dst; norm_num [Fin.coe_ofNat_eq_mod] at hdow
  let s1 := Function.update s 240 (encode a)
  let s2 := Function.update s1 241 (encode b)
  let s3 := Function.update s2 244 (encode (op a b))
  let s4 := Function.update s 244 (encode (op a b))
  let s5 := Function.update s4 dst (encode (op a b))
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have h1 : ExecutesIn (replace left 240) (9*W+8) s s1 := by
    simpa [s1, ha] using replace_bounded s left 240 W hl240 hl120 (by decide) h120
      (by simpa [ha] using hwidth a) (by simp [h240])
  have h2 : ExecutesIn (replace right 241) (9*W+8) s1 s2 := by
    simpa [s2, s1, hr240, hb] using replace_bounded s1 right 241 W hr241 hr120 (by decide)
      (by simp [s1, h120]) (by simpa [s1, hr240, hb] using hwidth b)
      (by simp [s1, h241])
  have h3 : ExecutesIn code K s2 s3 := hspec s2 a b hf2
    (by simp [s2, s1]) (by simp [s2]) (by simp [s2, s1, h244])
    (by simp [s2, s1, h245])
  have h4 : ExecutesIn (SubexpLocalCRTSetup.clearMany [240,241]) (2*(2*W+3)) s3 s4 := by
    have h := SubexpLocalCRTSetup.clearMany_run [240,241] s3 W (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simpa [s3, s2, s1] using hwidth a
      · simpa [s3, s2] using hwidth b)
    have he : SubexpLocalCRTSetup.cleared [240,241] s3 = s4 := by
      funext i
      by_cases h240i : i = 240 <;> by_cases h241i : i = 241 <;>
        simp [SubexpLocalCRTSetup.cleared_apply, s4, s3, s2, s1,
          Function.update_apply, h240i, h241i, h240, h241]
    simpa only [he, List.length_cons, List.length_nil] using h
  have h5 : ExecutesIn (replace 244 dst) (9*W+8) s4 s5 := by
    simpa [s5, s4] using replace_bounded s4 244 dst W (Ne.symm hd244) (by decide) hd120
      (by simp [s4, h120]) (by simpa [s4] using hwidth (op a b))
      (by simpa [s4, hd244] using hdlen)
  have h6 : ExecutesIn (clear 244) (2*W+3) s5
      (Function.update s dst (encode (op a b))) := by
    have h := clear_run 244 s5
    have he : Function.update s5 244 [] = Function.update s dst (encode (op a b)) := by
      funext i
      by_cases hi : i = 244 <;>
        simp [s5, s4, Function.update_apply, hi, h244, Ne.symm hd244]
    rw [he] at h
    apply h.mono
    simp [s5, s4, Ne.symm hd244]
    have hw := hwidth (op a b)
    omega
  exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono (by omega)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
