import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorAssembledBounds

namespace OAI.Algorithms

/-! Native call caps are derived from physically retained source words and
sparse support capacity, rather than being supplied as an independent oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorResource
open SubexponentialSAT SubexpLiftRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open IdempotentApplyProgram.Bounds

noncomputable def nativeCap {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A F : ℕ) : ℕ :=
  2*A+F+n+d+baseWidth 3 q.p.t+q.u+q.J+
    capacity (Finset.univ : Finset (Fin n)) q.u q.J+d*baseWidth 3 q.p.t+1

theorem rawInput_length {m : ℕ} (b : ℕ) (ts : List (Fin m × ZMod 3)) :
    (HashInputProgram.Loop.rawInput b ts).length=ts.length*b := by
  unfold HashInputProgram.Loop.rawInput
  rw [List.length_reverse]
  induction ts with
  | nil => simp
  | cons a ts ih =>
    simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_cons,
      HashInputProgram.Loop.word,fixedBits_length]
    nlinarith only [ih]

theorem nativeResources {r Q n d : ℕ} {q : Factor.Spec r Q n d} {S A : ℕ}
    {base : Fin 768 → List Bool} (h : FactorReady.Input q S A base) (F : ℕ) :
    FactorReady.Resources q base F (nativeCap q A F) := by
  have hA : A ≤ nativeCap q A F := by unfold nativeCap; omega
  have h2A : 2*A ≤ nativeCap q A F := by unfold nativeCap; omega
  have hB : baseWidth 3 q.p.t ≤ nativeCap q A F := by unfold nativeCap; omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · refine ⟨?_,q.p.hd,hB,?_,?_,?_,?_,?_,?_⟩
    · unfold nativeCap; omega
    · unfold nativeCap; omega
    · unfold nativeCap; omega
    · change q.u ≤ nativeCap q A F
      unfold nativeCap; omega
    · change q.J ≤ nativeCap q A F
      unfold nativeCap; omega
    · change capacity (Finset.univ : Finset (Fin n)) q.u q.J ≤ nativeCap q A F
      unfold nativeCap; omega
    · unfold nativeCap; omega
  · unfold nativeCap; omega
  · exact ((h.hashWidth ▸ h.size 708) : q.bitWidth ≤ A).trans hA
  · exact ((h.clauses ▸ h.size 700) : (Encoding.encodeList id q.clauses).length ≤ A).trans hA
  · intro ts hts
    have hm : (HashInputProgram.Loop.rawInput q.bitWidth ts).reverse ∈ q.rawRows :=
      List.mem_map.mpr ⟨ts,hts,rfl⟩
    have hl := HashInputProgram.Loop.original_payload_length_le q.rawRows _ hm
    rw [List.length_reverse,rawInput_length] at hl
    have ha := h.size 701
    rw [h.rows] at ha
    have hb := q.bitWidthPositive
    have hh : ts.length ≤ A := by nlinarith
    exact hh.trans hA
  · have ht : q.p.t ≤ baseWidth 3 q.p.t := by unfold baseWidth; nlinarith
    simpa only [Factor.Spec.digits,List.length_ofFn] using ht.trans hB
  · intro ls hls
    have hm : HashInputProgram.clausePayload ls ∈ q.clauses :=
      List.mem_map.mpr ⟨ls,hls,rfl⟩
    have hl := HashInputProgram.Loop.original_payload_length_le q.clauses _ hm
    have hc := Encoding.length_encodeList_lower (fun l => Encoding.encodeNat (Encoding.literalCode l)) ls
    have ha := h.size 700
    rw [h.clauses] at ha
    change ls.length+1 ≤ (HashInputProgram.clausePayload ls).length at hc
    have hh : ls.length ≤ A := by omega
    exact hh.trans hA
  · exact (payloadBound_le_base h).trans h2A
  · exact (h.size 707).trans hA

theorem nativeCap_le_work {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (A F U V k : ℕ) (p : CostAssembly.Resources)
    (hA : A ≤ U) (hF : F ≤ U) (hn : n ≤ V) (hd : d ≤ V)
    (hB : baseWidth 3 q.p.t ≤ V) (hu : q.u ≤ V) (hJ : q.J ≤ V)
    (horder : q.J ≤ CostAssembly.jetOrder k n p)
    (hbase : 0 < p.labelBase) (hheads : 1 ≤ p.heads) (hbits : 1 ≤ p.bits) :
    nativeCap q A F ≤ physicalEnvelope U V (CostAssembly.assembledWork k n p) := by
  have hc := capacity_le_work k n q.u q.J p horder hbase hheads hbits
  have hc' : capacity (Finset.univ : Finset (Fin n)) q.u q.J ≤
      V*V*CostAssembly.assembledWork k n p := hc.trans (by gcongr)
  have hwidth := Nat.mul_le_mul hd hB
  have hdiag : nativeCap q A F ≤ 3*U+5*V+V*V*CostAssembly.assembledWork k n p+V*V+1 := by
    unfold nativeCap
    omega
  apply hdiag.trans
  have hp : (V+1)^2 ≤ (V+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  let P := (U+1)*(V+1)^2*(CostAssembly.assembledWork k n p+1)
  have hsq : V ≤ (V+1)^2 := by nlinarith only []
  have hsq1 : 1 ≤ (V+1)^2 := Nat.one_le_pow _ _ (by omega)
  have huP : U ≤ P := by
    change U ≤ (U+1)*(V+1)^2*(CostAssembly.assembledWork k n p+1)
    calc
      U = U*1*1 := by ring
      _ ≤ _ := by gcongr <;> omega
  have hvP : V ≤ P := by
    change V ≤ (U+1)*(V+1)^2*(CostAssembly.assembledWork k n p+1)
    calc
      V = 1*V*1 := by ring
      _ ≤ _ := by gcongr <;> omega
  have hwP : V*V*CostAssembly.assembledWork k n p ≤ P := by
    change _ ≤ (U+1)*(V+1)^2*(CostAssembly.assembledWork k n p+1)
    calc
      _ = 1*(V*V)*CostAssembly.assembledWork k n p := by ring
      _ ≤ _ := by gcongr <;> nlinarith only []
  have hvvP : V*V ≤ P := by
    change _ ≤ (U+1)*(V+1)^2*(CostAssembly.assembledWork k n p+1)
    calc
      V*V = 1*(V*V)*1 := by ring
      _ ≤ _ := by gcongr <;> nlinarith only []
  have hP : 1 ≤ P := by
    unfold P
    have hu1 : 1 ≤ U+1 := by omega
    have hw1 : 1 ≤ CostAssembly.assembledWork k n p+1 := by omega
    exact Nat.mul_le_mul (Nat.mul_le_mul hu1 hsq1) hw1
  calc
    _ ≤ 12*(U+1)*(V+1)^2*(CostAssembly.assembledWork k n p+1) := by
      have hh : 3*U+5*V+V*V*CostAssembly.assembledWork k n p+V*V+1 ≤ 12*P := by omega
      simpa only [P,Nat.mul_assoc] using hh
    _ ≤ _ := by unfold physicalEnvelope; gcongr ; omega

end SubexponentialSAT.SqrtLog.LeafProgram.FactorResource

end OAI.Algorithms
