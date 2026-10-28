import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeWords
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramRelReadout

namespace OAI.Algorithms

/-! The generated preparation state has exactly the native arithmetic core. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing MomentsProgram MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem core_cleanup : ∀ i : Fin 56, corePorts i ∈ Node.cleanupPorts := by
  intro i
  apply (Node.mem_cleanup _).mpr
  left
  simp [corePorts]
  omega

private theorem core_not_low : ∀ i : Fin 56, corePorts i ∉ LayoutMasters.lowPorts := by
  intro i h
  obtain ⟨j, _, hj⟩ := List.mem_map.mp h
  have hv := congrArg Fin.val hj
  simp [corePorts, LayoutMasters.low] at hv
  omega

private theorem support_not_cache : ∀ i : Fin 768,
    (i ∈ ([160,161,164,168,174,175,176,178,179] : List (Fin 768)) ∨
      (180 ≤ i.val ∧ i.val ≤ 188)) → i ∉ LeafNodeCacheProgram.cachePorts := by
  intro i hi hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  simp [LeafNodeCacheProgram.cachePorts] at hc
  rcases hi with hi | hi
  · rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num at hc
  · omega

private theorem readout_cleanup : ∀ i : Fin 768, i ∈ readoutWorkPorts →
    i ∈ Node.cleanupPorts := by
  intro i hi
  apply (Node.mem_cleanup _).mpr
  simp [readoutWorkPorts] at hi
  omega

private theorem readout_not_low : ∀ i : Fin 768, i ∈ readoutWorkPorts →
    i ∉ LayoutMasters.lowPorts := by
  intro i hi hm
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hm
  have hv := congrArg Fin.val hj
  simp [LayoutMasters.low] at hv
  simp [readoutWorkPorts] at hi
  omega

private theorem readout_not_cache : ∀ i : Fin 768, i ∈ readoutWorkPorts →
    i ∉ LeafNodeCacheProgram.cachePorts := by
  intro i hi hc
  simp [readoutWorkPorts] at hi
  simp [LeafNodeCacheProgram.cachePorts] at hc
  omega

private theorem readout_not_special : ∀ i : Fin 768, i ∈ readoutWorkPorts →
    i ∉ ([78,163,169,710,711,712] : List (Fin 768)) := by
  intro i hi hs
  simp [readoutWorkPorts] at hi
  simp at hs
  omega

theorem Preparation.direct_master {s : HeadInputs} {a d : Data} (pr : Preparation s a d)
    (ha : Ready s a) (q : Fin 768 × Fin 768) (hq : q∈LeafNodeCacheProgram.directCopies)
    (hg : 142 ≤ q.1.val) : d.stacks q.2=a.stacks q.1 :=
  (pr.direct_word ha q hq).trans
    (LayoutMasters.loaded_frame (LayoutMasters.project a) q.1 (not_low_of_ge hg))

theorem Preparation.core_words {s : HeadInputs} {a b : Data} (pr : Preparation s a b)
    (ha : Ready s a) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (u J : ℕ)
    (h194 : a.stacks 194=M.bits) (h201 : a.stacks 201=RingTriple.tableEncoding table)
    (h202 : a.stacks 202=width) (h203 : a.stacks 203=cache.zero.val)
    (h204 : a.stacks 204=degree) (h212 : a.stacks 212=List.replicate u true)
    (h243 : a.stacks 243=List.replicate J true) :
    ∀ i : Fin 56, b.stacks (corePorts i)=
      Product.tapes (emptyCore (Product.environment p t M cache table degree width u J)) i := by
  have h5 := (pr.direct_master ha (194,5) (by decide) (by decide)).trans h194
  have h12 := (pr.direct_master ha (202,12) (by decide) (by decide)).trans h202
  have h17 := (pr.direct_master ha (203,17) (by decide) (by decide)).trans h203
  have h22 := (pr.direct_master ha (201,22) (by decide) (by decide)).trans h201
  have h39 := (pr.direct_master ha (204,39) (by decide) (by decide)).trans h204
  have h45 := (pr.direct_master ha (212,45) (by decide) (by decide)).trans h212
  have h46 := (pr.direct_master ha (243,46) (by decide) (by decide)).trans h243
  intro i
  fin_cases i <;> simp only [corePorts,Product.tapes,emptyCore,Product.environment,Product.idle]
  all_goals first
    | exact h5 | exact h12 | exact h17 | exact h22 | exact h39 | exact h45 | exact h46
    | exact pr.empty_word ha _ (core_cleanup _) (core_not_low _) (by decide) (by decide)

theorem machine_self (a : Data) (e : Product.Store)
    (hc : ∀ i : Fin 56,a.stacks (corePorts i)=Product.tapes e i) :
    machine a.regs e a.stacks=a := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : i.val < 56
    · let j : Fin 56 := ⟨i.val,hi⟩
      have hj : corePorts j=i := Fin.ext rfl
      simpa only [machine,hi,↓reduceDIte,j,hj] using (hc j).symm
    · simp [hi]

theorem Preparation.support_clean {s : HeadInputs} {a b : Data} (pr : Preparation s a b)
    (ha : Ready s a) : SupportClean b.stacks := by
  intro i hi
  have hv : 160 ≤ i.val ∧ i.val ≤ 188 := by
    rcases hi with hi|hi
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
    · omega
  apply pr.empty_word ha i
  · apply (Node.mem_cleanup _).mpr; omega
  · exact not_low_of_ge (by omega)
  · exact support_not_cache i hi
  · intro hm
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [Fin.ext_iff] at hi

theorem Preparation.readout_clean {s : HeadInputs} {a b : Data} (pr : Preparation s a b)
    (ha : Ready s a) : ∀ i∈readoutWorkPorts,b.stacks i=[] := by
  intro i hi
  exact pr.empty_word ha i (readout_cleanup i hi) (readout_not_low i hi)
    (readout_not_cache i hi) (readout_not_special i hi)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
