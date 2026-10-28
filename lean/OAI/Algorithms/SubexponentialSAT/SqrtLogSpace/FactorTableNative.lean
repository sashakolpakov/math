import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTablePayloadMeaning
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpecialization
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceReady
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyStaging
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblySourceCall
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyOutputBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceNativeCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeMaskDecode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramBounds

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

structure ScalarMasters (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J R : ℕ) (theta : Coeff (baseWidth 3 t) d) (s : OuterData) (n : ℕ) : Prop where
  widthPositive : 0<baseWidth 3 t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val<3^t
  zeroBits : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
    List.replicate (d*baseWidth 3 t) false
  modulus : s.stacks 194=M.bits
  width : (s.stacks 202).length=baseWidth 3 t
  zero : s.stacks 203=cache.zero.val
  table : s.stacks 201=RingTriple.tableEncoding (HornerProgram.modelTable t a M cache)
  degree : (s.stacks 204).length=d
  choicesLength : (s.stacks 145).length=n
  zeroWord : s.stacks 280=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  oneWord : s.stacks 207=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  thetaWord : s.stacks 78=RingProgram.flat theta
  ambientCount : s.stacks 128=List.replicate n true
  targetCount : s.stacks 243=List.replicate J true
  radius : s.stacks 138=List.replicate R true
  highLength : (s.stacks 703).length=n

structure SourceMasters {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : SourceReady.Data) : Prop where
  colors : a.stacks 130=List.replicate r true
  nodes : a.stacks 131=List.replicate Q true
  typeWidth : a.stacks 132=List.replicate (Q*r) true
  positive : a.stacks 710=p.saved.hp
  negative : a.stacks 711=p.saved.hn
  scalarWidth : a.stacks 140=p.width
  power : a.stacks 712=p.power.1
  powerNegative : p.power.2=[]
  radius : a.stacks 138=List.replicate p.R true
  offset : a.stacks 139=p.aWord
  metadata : a.stacks 135=SelectorProgram.rawRecords
    (PackingMetadata.records P (fun v=>List.replicate v.val true) CollisionProgram.encodeType)
  plans : a.stacks 136=LayoutOwnerFiberProgram.stream ps
  inverses : a.stacks 713=(List.ofFn (fun i=>RingProgram.flat (p.inverse i))).flatten
  negatives : a.stacks 714=(List.ofFn (fun i=>RingProgram.flat (p.negative i))).flatten
  differences : a.stacks 715=(List.ofFn (fun i=>
    (List.ofFn (fun j=>RingProgram.flat (p.difference i j))).flatten)).flatten
  ringWidth : a.stacks 717=p.ringWidth
  rowWidth : a.stacks 716=p.rowWidth
  zero : a.stacks 280=RingProgram.flat p.ops.zeroRun.1
  one : a.stacks 207=RingProgram.flat p.ops.oneRun.1
  minusOne : a.stacks 211=RingProgram.flat p.minusOne
  inverseDenominator : a.stacks 728=RingProgram.flat p.invDenom


/-- Entry clearing reconstructs the ordinary caller cleanliness rather than
assuming the private worker survived a previous head reload. -/
theorem ScalarMasters.initialized {t d J R n : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d}
    (a : FactorTableProgram.OuterData)
    (h : ScalarMasters t model M cache J R theta
      (projectState id FactorTableProgram.basePort a) n) :
    CallerInput t model M cache J R theta
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)) n := by
  have frame (i : Fin 768) (hi : (i.val < 340 ∧ i ≠ 62) ∨ 684 < i.val) :
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)).stacks i =
        (projectState id FactorTableProgram.basePort a).stacks i :=
    FactorTableSpace.initialized_base_external a i hi
  refine ⟨h.widthPositive,h.zeroCanonical,h.zeroBits,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [frame 194 (by decide)]; exact h.modulus
  · rw [frame 202 (by decide)]; exact h.width
  · rw [frame 203 (by decide)]; exact h.zero
  · rw [frame 201 (by decide)]; exact h.table
  · rw [frame 204 (by decide)]; exact h.degree
  · rw [frame 145 (by decide)]; exact h.choicesLength
  · rw [frame 280 (by decide)]; exact h.zeroWord
  · rw [frame 207 (by decide)]; exact h.oneWord
  · rw [frame 78 (by decide)]; exact h.thetaWord
  · rw [frame 128 (by decide)]; exact h.ambientCount
  · rw [frame 243 (by decide)]; exact h.targetCount
  · rw [frame 138 (by decide)]; exact h.radius
  · rw [frame 703 (by decide)]; exact h.highLength
  · intro i hlo hhi hn
    exact FactorTableProgram.initialized_empty a i hlo hhi hn

/-- Every source master lies outside the concretely cleared private bank. -/
theorem SourceMasters.initialized {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    (a : FactorTableProgram.OuterData)
    (h : SourceMasters p ps P (projectState id FactorTableProgram.basePort a)) :
    SourceMasters p ps P
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)) := by
  have frame (i : Fin 768) (hi : (i.val < 340 ∧ i ≠ 62) ∨ 684 < i.val) :
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)).stacks i =
        (projectState id FactorTableProgram.basePort a).stacks i :=
    FactorTableSpace.initialized_base_external a i hi
  constructor
  · rw [frame 130 (by decide)]; exact h.colors
  · rw [frame 131 (by decide)]; exact h.nodes
  · rw [frame 132 (by decide)]; exact h.typeWidth
  · rw [frame 710 (by decide)]; exact h.positive
  · rw [frame 711 (by decide)]; exact h.negative
  · rw [frame 140 (by decide)]; exact h.scalarWidth
  · rw [frame 712 (by decide)]; exact h.power
  · exact h.powerNegative
  · rw [frame 138 (by decide)]; exact h.radius
  · rw [frame 139 (by decide)]; exact h.offset
  · rw [frame 135 (by decide)]; exact h.metadata
  · rw [frame 136 (by decide)]; exact h.plans
  · rw [frame 713 (by decide)]; exact h.inverses
  · rw [frame 714 (by decide)]; exact h.negatives
  · rw [frame 715 (by decide)]; exact h.differences
  · rw [frame 717 (by decide)]; exact h.ringWidth
  · rw [frame 716 (by decide)]; exact h.rowWidth
  · rw [frame 280 (by decide)]; exact h.zero
  · rw [frame 207 (by decide)]; exact h.one
  · rw [frame 211 (by decide)]; exact h.minusOne
  · rw [frame 728 (by decide)]; exact h.inverseDenominator

theorem staged_external (a : SourceReady.Data) (i : Fin 768)
    (hi : i.val < 340 ∨ 680 ≤ i.val) : (Incidence.staged a).stacks i=a.stacks i := by
  apply Incidence.staged_frame
  · intro he; subst i; norm_num at hi
  · intro p hp
    have hb : 340 ≤ p.2.val ∧ p.2.val < 680 := by
      simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    intro he
    subst i
    omega

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

theorem source_of_staged (h : CallerInput p.t p.model p.modulus p.cache J p.R theta a n)
    (hm : SourceMasters p ps P a)
    (hf : a.stacks 556=List.replicate f true) (htmp : a.stacks 684=[])
    (hback : ∀ i∈SourceStaging.backupPorts,a.stacks i=[])
    (hsize : WordBound S (Incidence.staged a))
    (harray : (p.R+1)*(d*baseWidth 3 p.t) ≤ S) (hcount : p.R+1 ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hinc : ps.length ≤ S) :
    SourceReady.Input p ps P (Incidence.staged a) 0 n f S := by
  have hc := Incidence.staged_copy a h.destinations_empty
  have hex := staged_external a
  have hclean : ∀ i : Fin 340,i∉SourceReady.physicalLive →
      (Incidence.staged a).stacks (SourceReady.localPort i)=[] := by
    intro i hi
    have h550 : SourceReady.localPort i≠550 := by
      intro he
      have hv : i=210 := Fin.ext (by have := congrArg Fin.val he; dsimp [SourceReady.localPort] at this; omega)
      exact hi (by simp [hv,SourceReady.physicalLive])
    have hdest : ∀ z∈Incidence.pairs,SourceReady.localPort i≠z.2 := by
      intro z hz he
      have hv := congrArg Fin.val he
      simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals dsimp [SourceReady.localPort] at hv
      all_goals apply hi; simp only [SourceReady.physicalLive,List.mem_cons,List.mem_nil_iff,or_false]
      all_goals simp only [Fin.ext_iff,Fin.coe_ofNat_eq_mod]; omega
    rw [Incidence.staged_frame a _ h550 hdest]
    apply h.workerEmpty
    · dsimp [SourceReady.localPort]; omega
    · dsimp [SourceReady.localPort]; omega
    · intro he
      have hv : i=216 := Fin.ext (by have := congrArg Fin.val he; dsimp [SourceReady.localPort] at this; omega)
      exact hi (by simp [hv,SourceReady.physicalLive])
  have hfactor : (Incidence.staged a).stacks 556=List.replicate f true := by
    rw [Incidence.staged_frame a 556 (by decide) (by
      intro z hz
      simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    exact hf
  refine ⟨h.staged.arithmetic,hclean,(hex 684 (Or.inr (by decide))).trans htmp,?_,?_,?_,hfactor,?_,
    ?_,?_,?_,?_,?_,?_,?_,hm.powerNegative,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    hsize,harray,hcount,hmetadata,hinc⟩
  · intro i hi
    have hg : 680 ≤ i.val := by
      simp only [SourceStaging.backupPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide
    exact (hex i (Or.inr hg)).trans (hback i hi)
  · exact Incidence.staged_cutoff a p.R h.radius (h.workerEmpty 550 (by decide) (by decide) (by decide))
  · exact (hc (128,552) (by decide)).trans h.ambientCount
  · exact h.staged_empty 573 (by decide)
  · exact (hex _ (Or.inl (by decide))).trans hm.colors
  · exact (hex _ (Or.inl (by decide))).trans hm.nodes
  · exact (hex _ (Or.inl (by decide))).trans hm.typeWidth
  · exact (hex _ (Or.inr (by decide))).trans hm.positive
  · exact (hex _ (Or.inr (by decide))).trans hm.negative
  · exact (hex _ (Or.inl (by decide))).trans hm.scalarWidth
  · exact (hex _ (Or.inr (by decide))).trans hm.power
  · exact (hex _ (Or.inl (by decide))).trans hm.radius
  · exact (hex _ (Or.inl (by decide))).trans hm.offset
  · exact (hex _ (Or.inl (by decide))).trans hm.metadata
  · exact (hex _ (Or.inl (by decide))).trans hm.plans
  · exact (hex _ (Or.inr (by decide))).trans hm.inverses
  · exact (hex _ (Or.inr (by decide))).trans hm.negatives
  · exact (hex _ (Or.inr (by decide))).trans hm.differences
  · exact (hex _ (Or.inr (by decide))).trans hm.ringWidth
  · exact (hex _ (Or.inr (by decide))).trans hm.rowWidth
  · exact (hex _ (Or.inl (by decide))).trans hm.zero
  · exact (hex _ (Or.inl (by decide))).trans hm.one
  · exact (hex _ (Or.inl (by decide))).trans hm.minusOne
  · exact (hex _ (Or.inr (by decide))).trans hm.inverseDenominator




/-- One iteration carries the actual original-variable counter, retained
lookup accumulator and its unary key into the source call. -/
def sourceCallData (s : FactorTableProgram.OuterStore) (j : ℕ) (acc : List Bool)
    (regs : Fin 16 → Bool) : FactorTableProgram.OuterData :=
  ⟨regs, Function.update (FactorTableProgram.literalReady s (List.replicate j true) acc)
    555 (Encoding.encodeNat j)⟩

theorem sourceCallData_wordBound (s : FactorTableProgram.OuterStore) (B n L j : ℕ)
    (acc : List Bool) (regs : Fin 16 → Bool)
    (hbase : ∀ i, (s i).length ≤ B) (hj : j < n)
    (hacc : acc.length ≤ n * FactorTableProgram.literalRecordBound n L) :
    ∀ i, ((sourceCallData s j acc regs).stacks i).length ≤
      B + n + n * FactorTableProgram.literalRecordBound n L + 1 := by
  intro i
  by_cases h555 : i = 555
  · subst i
    simp only [sourceCallData, Function.update_self, Encoding.length_encodeNat]
    omega
  by_cases h569 : i = 569
  · subst i
    simpa [sourceCallData, FactorTableProgram.literalReady] using
      hacc.trans (by omega : n * FactorTableProgram.literalRecordBound n L ≤
        B + n + n * FactorTableProgram.literalRecordBound n L + 1)
  by_cases h573 : i = 573
  · subst i
    simp [sourceCallData, FactorTableProgram.literalReady]
    omega
  simp only [sourceCallData, FactorTableProgram.literalReady, Function.update_of_ne h555,
    Function.update_of_ne h569, Function.update_of_ne h573]
  exact (hbase i).trans (by omega)

theorem project_sourceCallData (s : FactorTableProgram.OuterStore) (j : ℕ) (acc : List Bool)
    (regs : Fin 16 → Bool) :
    projectState id FactorTableProgram.basePort (sourceCallData s j acc regs) =
      PerturbationAssembly.sourceCallData (FactorTableProgram.projectBase s) j acc regs := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · change FactorTableProgram.projectBase (Function.update
      (Function.update (Function.update s (FactorTableProgram.basePort 573) (List.replicate j true))
        (FactorTableProgram.basePort 569) acc) (FactorTableProgram.basePort 555) (Encoding.encodeNat j)) = _
    rw [FactorTableProgram.projectBase_update, FactorTableProgram.projectBase_update, FactorTableProgram.projectBase_update]
    rfl

theorem project_staged (a : FactorTableProgram.OuterData) :
    projectState id FactorTableProgram.basePort (FactorTableProgram.staged a) =
      Incidence.staged (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)) := by
  exact projectState_embed id FactorTableProgram.basePort _ _ Function.injective_id FactorTableProgram.basePort_injective

/-- A physical source invariant before the loop supplies every relocated
source call, including its actual candidate index and polynomial table word. -/
theorem sourceInput_at_call {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : FactorTableProgram.OuterData) (v n f S j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool)
    (h : SourceReady.Input p ps P (projectState id FactorTableProgram.basePort a) v n f S)
    (hsize : ∀ i, ((sourceCallData a.stacks j acc regs).stacks i).length ≤ S) :
    SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort (sourceCallData a.stacks j acc regs)) j n f S := by
  rw [project_sourceCallData]
  exact PerturbationAssembly.sourceInput_at_call p ps P
    (projectState id FactorTableProgram.basePort a) v n f S j acc regs h (fun i => by
      have hh := hsize (FactorTableProgram.basePort i)
      change ((projectState id FactorTableProgram.basePort (sourceCallData a.stacks j acc regs)).stacks i).length ≤ S at hh
      rw [project_sourceCallData] at hh
      exact hh)

/-- The old source-row arithmetic input is exactly the low projection of
the relocated call state; its variable choices still have ambient length n. -/
theorem rowInput_at_call (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N n : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (s : FactorTableProgram.OuterStore)
    (h : StagedInput t model M cache J N theta (FactorTableProgram.projectBase s) n)
    (xs : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N))
    (hx : xs.length = n) (j : ℕ) (hj : j < n) (acc : List Bool)
    (regs : Fin 16 → Bool) :
    LowInput t model M cache J N theta (pairChoice xs (s 546))
      (FactorTableProgram.projectInner
        (Function.update (sourceCallData s j acc regs).stacks 545
          (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs))) := by
  have hp : FactorTableProgram.projectBase
      (Function.update (sourceCallData s j acc regs).stacks 545
        (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs)) =
      literalSourceState
        (literalReady (FactorTableProgram.projectBase s) (List.replicate j true) acc)
        j (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs) := by
    change FactorTableProgram.projectBase
      (Function.update (Function.update
        (Function.update (Function.update s (FactorTableProgram.basePort 573)
          (List.replicate j true)) (FactorTableProgram.basePort 569) acc)
          (FactorTableProgram.basePort 555) (Encoding.encodeNat j))
          (FactorTableProgram.basePort 545) _) = _
    rw [FactorTableProgram.projectBase_update, FactorTableProgram.projectBase_update,
      FactorTableProgram.projectBase_update, FactorTableProgram.projectBase_update]
    rfl
  have hh := h.rowInput xs hx j hj acc
  rw [← hp, FactorTableProgram.projectInner_projectBase] at hh
  exact hh

/-- Actual SourceReady cleanliness supplies the immediate producer's high
scratch bank. The eight relocated source-local masters are outside this bank. -/
theorem source_high_empty {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : FactorTableProgram.OuterData) (v n f S : ℕ)
    (h : SourceReady.Input p ps P (projectState id FactorTableProgram.basePort a) v n f S)
    (i : Fin 38) :
    a.stacks (FactorTableProgram.joinedPort (QueryProducerSpace.Native.producerPorts i)) = [] := by
  let j : Fin 340 := ⟨256+i.val, by omega⟩
  have hj : j ∉ SourceReady.physicalLive := by
    intro hm
    simp only [SourceReady.physicalLive, List.mem_cons, List.mem_nil_iff, or_false,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hm
    dsimp only [j] at hm
    omega
  have he := h.clean j hj
  have hp : FactorTableProgram.basePort (SourceReady.localPort j) =
      FactorTableProgram.joinedPort (QueryProducerSpace.Native.producerPorts i) := by
    rw [FactorTableProgram.basePort_low _ (by
      change 340+(256+i.val)<640
      have hi := i.isLt
      omega)]
    apply Fin.ext
    rfl
  change a.stacks (FactorTableProgram.basePort (SourceReady.localPort j)) = [] at he
  rwa [hp] at he

/-- The generalized factor identifier is retained through paid staging;
all native source prerequisites follow from concrete stored masters. -/
theorem source_of_remapped_staged {r Q d n J S f : ℕ}
    (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : FactorTableProgram.OuterData) (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (h : CallerInput p.t p.model p.modulus p.cache J p.R theta
      (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)) n)
    (hm : SourceMasters p ps P (projectState id FactorTableProgram.basePort (FactorTableProgram.initialized a)))
    (hf : a.stacks 556 = List.replicate f true)
    (hsize : WordBound S (projectState id FactorTableProgram.basePort (FactorTableProgram.staged a)))
    (harray : (p.R+1)*(d*baseWidth 3 p.t) ≤ S) (hcount : p.R+1 ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hinc : ps.length ≤ S) :
    SourceReady.Input p ps P (projectState id FactorTableProgram.basePort (FactorTableProgram.staged a)) 0 n f S := by
  rw [project_staged] at hsize ⊢
  apply source_of_staged h hm
  · simpa only [projectState, Function.comp_apply,
      show FactorTableProgram.basePort 556 = (556 : Fin 896) from rfl, FactorTableProgram.initialized_selected] using hf
  · simpa only [projectState, Function.comp_apply,
      show FactorTableProgram.basePort 684 = (684 : Fin 896) from rfl] using FactorTableProgram.initialized_temporary a
  · intro i hi
    simp only [SourceStaging.backupPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      simp only [projectState, Function.comp_apply]
      rw [FactorTableProgram.initialized, clearMany_stacks, ite_eq_left]
      exact List.mem_append_right _ (by decide)
  · exact hsize
  · exact harray
  · exact hcount
  · exact hmetadata
  · exact hinc


/-- Initial physical masters and their measured word sizes establish source
readiness after the actual clear-and-stage commands, for the chosen factor. -/
theorem source_of_masters {r Q d n J S f B : ℕ}
    (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : FactorTableProgram.OuterData) (theta : Coeff (baseWidth 3 p.t) d)
    (hscalar : ScalarMasters p.t p.model p.modulus p.cache J p.R theta
      (projectState id FactorTableProgram.basePort a) n)
    (hmasters : SourceMasters p ps P (projectState id FactorTableProgram.basePort a))
    (hf : a.stacks 556 = List.replicate f true)
    (hincoming : ∀ i, (a.stacks i).length ≤ B)
    (hsize : 1029*B+99 ≤ S)
    (harray : (p.R+1)*(d*baseWidth 3 p.t) ≤ S) (hcount : p.R+1 ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hinc : ps.length ≤ S) :
    SourceReady.Input p ps P (projectState id FactorTableProgram.basePort
      (FactorTableProgram.staged a)) 0 n f S := by
  apply source_of_remapped_staged p ps P a theta (hscalar.initialized a)
    (hmasters.initialized a) hf
  · intro i
    exact (FactorTableSpace.staged_stack_bound a B hincoming
      (FactorTableProgram.basePort i)).trans hsize
  · exact harray
  · exact hcount
  · exact hmetadata
  · exact hinc

/-- The concrete native source program supplies its own row witness and full
source polynomial identity. No row oracle or execution is an input. -/
theorem native_source_run {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : FactorTableProgram.OuterData) (v n f S : ℕ)
    (h : SourceReady.Input p ps P (projectState id FactorTableProgram.basePort a) v n f S)
    (hv : v ≤ S) (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S) :
    ∃ (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)))
      (k : ℕ) (rr : Fin 16 → Bool),
      rows.length = n ∧
      LayoutSourceRowsProgram.RowProperty DensePolynomialProgram.Fixed.encode
        (fun j out => PolynomialExecutorProgram.meaning p.ops out.val =
          LayoutSourceRowsProgram.sourceRowFamily ps n f v
            (LayoutSourceRowsProgram.totalPackedSource p P) j)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧
      k ≤ Source.nativeSourceWorkPolynomial p S + 1 ∧
      Eval (FactorTableProgram.liftBase Source.command) k a
        (⟨rr,Function.update a.stacks 545
          (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : FactorTableProgram.OuterData) := by
  obtain ⟨rows,k,rr,hlen,hrows,hk,he⟩ := Source.native_command_bound p ps P
    (projectState id FactorTableProgram.basePort a) v n f S _ _ h.native h.size hv hn hf hplans
      h.call_bounds.1 h.call_bounds.2
  have hl := eval_liftCommand_from_state Source.command 0 0 id FactorTableProgram.basePort a
    Function.injective_id FactorTableProgram.basePort_injective he
  have ho : embedState id FactorTableProgram.basePort a
      (⟨rr, Function.update (projectState id FactorTableProgram.basePort a).stacks 545
        (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : SourceReady.Data) =
      (⟨rr,Function.update a.stacks 545
        (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : FactorTableProgram.OuterData) := by
    apply SubexpScanPrimitives.state_ext
    · simp [embedState]
    · change FactorTableProgram.replaceBase a.stacks (Function.update (FactorTableProgram.projectBase a.stacks) 545 _) = _
      rw [FactorTableProgram.replaceBase_update, FactorTableProgram.replaceBase_project]
      rfl
  rw [ho] at hl
  exact ⟨rows,k+1,rr,hlen,hrows,Nat.add_le_add_right hk 1,hl⟩


/-- Source output545 replaces only local205; scalar/cache words used by the
immediate producer retain the size bound of the actual source input. -/
theorem source_output_cache_bound (a : FactorTableProgram.OuterData) (words : List Bool)
    (S : ℕ) (hb : ∀ i, ((projectState id FactorTableProgram.basePort a).stacks i).length ≤ S)
    (i : Fin 256) (hi : i ≠ 205) :
    ((FactorTableProgram.projectInner (Function.update a.stacks 545 words)) i).length ≤ S := by
  have hn : FactorTableProgram.innerPort i ≠ 545 := by
    intro h
    apply hi
    exact FactorTableProgram.innerPort_injective h
  have hh := hb (PerturbationAssembly.innerPort i)
  change (a.stacks (FactorTableProgram.basePort (PerturbationAssembly.innerPort i))).length ≤ S at hh
  rw [FactorTableProgram.basePort_inner] at hh
  simpa only [FactorTableProgram.projectInner, Function.comp_apply, Function.update_of_ne hn] using hh

theorem good_bytes_transport {m n B d u J : ℕ} (hm : m = n)
    (entries : List (MomentsProgram.Product.Entry m B d))
    (hgood : TruncatedRingProgram.Good ∅ u J entries) :
    ∃ result : List (MomentsProgram.Product.Entry n B d),
      TruncatedRingProgram.Good ∅ u J result ∧
      MomentsProgram.Product.bytes entries = MomentsProgram.Product.bytes result := by
  subst n
  exact ⟨entries, hgood, rfl⟩

def specializedPayloadBound (n u J B d : ℕ) : ℕ :=
  u*J*(2*(u+J+n)+2*(d*B)+2)

def specializedRawBound (n u J B d : ℕ) : ℕ :=
  (1+n*(J-1)) * (2*(u+J+n)+2*(d*B)+2)

def specializedWorkPolynomial (t d u J N n S : ℕ) : ℕ :=
  3200000 * (lowWorkPolynomial n N J t d (3*S) + 3*S +
    specializedRawBound n u J (baseWidth 3 t) d + n + baseWidth 3 t + d + u + J +
    (1+n*(J-1)) + 1)^10

/-- The nested actual emitter and specializer budgets have a fixed degree,
independent of every runtime scalar, word, assignment and factor index. -/
theorem specializedWorkPolynomial_bound (t d u J N n S : ℕ) :
    specializedWorkPolynomial t d u J N n S ≤
      (3200000 * (1000000000*3^10+64)^10) *
        (n+N+J+d+baseWidth 3 t+u+S+1)^100 := by
  let A := n+N+J+d+baseWidth 3 t+u+S+1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hn : n ≤ A := by dsimp [A]; omega
  have hJ : J ≤ A := by dsimp [A]; omega
  have hd : d ≤ A := by dsimp [A]; omega
  have hB : baseWidth 3 t ≤ A := by dsimp [A]; omega
  have hu : u ≤ A := by dsimp [A]; omega
  have hS : S ≤ A := by dsimp [A]; omega
  have hj : J-1 ≤ A := (Nat.sub_le J 1).trans hJ
  have hlow := QueryProducerSpace.lowWork_polynomial n N J t d (3*S)
  have hlow' : lowWorkPolynomial n N J t d (3*S) ≤
      1000000000*(3*A)^10 := by
    apply hlow.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp [A]
    omega
  have hm : lowWorkPolynomial n N J t d (3*S) + 3*S +
      specializedRawBound n u J (baseWidth 3 t) d + n + baseWidth 3 t + d + u + J +
      (1+n*(J-1)) + 1 ≤
      1000000000*(3*A)^10 + 3*A +
      (1+A*A)*(2*(A+A+A)+2*(A*A)+2) + A+A+A+A+A+(1+A*A)+1 := by
    unfold specializedRawBound
    gcongr
  have h0 : 1 ≤ A^10 := Nat.one_le_pow 10 A hA
  have h1 : A ≤ A^10 := by simpa using pow_le_pow_right' hA (show 1 ≤ 10 by decide)
  have h2 : A^2 ≤ A^10 := pow_le_pow_right' hA (by decide)
  have h3 : A^3 ≤ A^10 := pow_le_pow_right' hA (by decide)
  have h4 : A^4 ≤ A^10 := pow_le_pow_right' hA (by decide)
  have hinner : lowWorkPolynomial n N J t d (3*S) + 3*S +
      specializedRawBound n u J (baseWidth 3 t) d + n + baseWidth 3 t + d + u + J +
      (1+n*(J-1)) + 1 ≤ (1000000000*3^10+64)*A^10 := by
    apply hm.trans
    ring_nf
    omega
  have hp := Nat.mul_le_mul_left 3200000 (Nat.pow_le_pow_left hinner 10)
  simpa only [specializedWorkPolynomial,mul_pow,←pow_mul,
    show 10*10=100 from rfl,Nat.mul_assoc,A] using hp

theorem lowWorkPolynomial_mono_size (n N J t d E F : ℕ) (h : E ≤ F) :
    lowWorkPolynomial n N J t d E ≤ lowWorkPolynomial n N J t d F := by
  dsimp only [lowWorkPolynomial]
  omega

/-- All source and normalizer costs use one fixed polynomial degree. -/
theorem specializeBudget_le (t d u J N n S rawLength : ℕ)
    (low : Fin 256 → List Bool)
    (h192 : (low 192).length ≤ S) (h193 : (low 193).length ≤ S)
    (h243 : (low 243).length ≤ S) (h194 : (low 194).length ≤ S)
    (h202 : (low 202).length ≤ S) (h204 : (low 204).length ≤ S)
    (hraw : rawLength ≤ specializedRawBound n u J (baseWidth 3 t) d) :
    FactorTableProgram.specializeBudget t d u J N n (1+n*(J-1)) rawLength low ≤
      specializedWorkPolynomial t d u J N n S := by
  have he : (low 192).length+(low 193).length+(low 243).length ≤ 3*S := by omega
  have hp := lowWorkPolynomial_mono_size n N J t d _ _ he
  have hb := QueryProducerSpace.Native.combinedBudget_polynomial
    (lowWorkPolynomial n N J t d ((low 192).length+(low 193).length+(low 243).length))
    ((low 194).length+(low 202).length+(low 204).length)
    rawLength n (baseWidth 3 t) d u J (1+n*(J-1))
  apply hb.trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

/-- The emitted origin/singleton dictionary is polynomial before immediate
specialization, regardless of how many correction supports exist globally. -/
theorem emittedSource_bytes_bound (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool)) :
    (MomentsProgram.Product.bytes
      (QueryProducerSpace.emittedSource t model M cache J N theta rows)).length ≤
      specializedRawBound rows.length u J (baseWidth 3 t) d := by
  exact QueryProducerSpace.incidence_bytes_length
    (RingProgram.modelRing t ht hd model M cache) u J hu hJ theta
    (PerturbationBetaProgram.runValue t model M cache theta (pairedRows rows))
    (fun v : Fin rows.length => rows[v].1.val)

/-- Source rows are generated on this invocation and immediately specialized
using the retained ambient mask. The only returned words are row serialization
545 and the already-specialized dictionary557 consumed by finishLiteral. -/
theorem lowPayload_native_run {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f S j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (s : FactorTableProgram.OuterStore) (acc : List Bool) (regs : Fin 16 → Bool)
    (hcommon : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
      (FactorTableProgram.projectBase s) n)
    (hsource : SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort (sourceCallData s j acc regs)) j n f S)
    (hj : j < n) (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hmask : (s 857).length = n) (htmp : s 881 = []) :
    ∃ xs : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)),
      xs.length = n ∧
      LayoutSourceRowsProgram.RowProperty DensePolynomialProgram.Fixed.encode
        (fun z out => PolynomialExecutorProgram.meaning p.ops out.val =
          LayoutSourceRowsProgram.sourceRowFamily ps n f j
            (LayoutSourceRowsProgram.totalPackedSource p P) z)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 xs ∧
      let pairs := pairChoice xs (s 546)
      let source := QueryProducerSpace.emittedSource p.t p.model p.modulus p.cache
        J (p.R+1) theta pairs
      let result := MomentsProgram.Normalize.run 3 p.t p.modulus p.cache
        (HeadEvaluation.specializeEntries (Squarefree.decodeMask pairs.length (s 857)) source) []
      ∃ k rf, k ≤ Source.nativeSourceWorkPolynomial p S + 1 +
          (7*n+5+FactorTableProgram.specializeBudget p.t d u J (p.R+1) pairs.length
            (1+pairs.length*(J-1)) (MomentsProgram.Product.bytes source).length
            (FactorTableProgram.projectInner
              (Function.update (sourceCallData s j acc regs).stacks 545
                (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs)))) ∧
        TruncatedRingProgram.Good ∅ u J result ∧
        Eval FactorTableProgram.lowPayload k (sourceCallData s j acc regs)
          (⟨rf,Function.update
            (Function.update (sourceCallData s j acc regs).stacks 545
              (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs))
            557 (MomentsProgram.Product.bytes result)⟩ : FactorTableProgram.OuterData) := by
  let a := sourceCallData s j acc regs
  obtain ⟨xs, ns, rs, hxs, hrows, hns, hes⟩ :=
    native_source_run p ps P a j n f S hsource (hj.le.trans hn) hn hf hplans
  let pairs := pairChoice xs (s 546)
  have hchoices : (s 546).length = n := hcommon.choicesLength
  have hpairs : pairs.length = n :=
    (pairChoice_length xs (s 546) (hxs.trans hchoices.symm)).trans hxs
  let words := Encoding.encodeList DensePolynomialProgram.Fixed.encode xs
  let b : FactorTableProgram.OuterData := ⟨rs, Function.update a.stacks 545 words⟩
  let low := FactorTableProgram.projectInner b.stacks
  have hin : LowInput p.t p.model p.modulus p.cache J (p.R+1) theta pairs low :=
    rowInput_at_call p.t p.model p.modulus p.cache J (p.R+1) n theta s hcommon xs hxs
      j hj acc regs
  have hz : low 217 = [] := by
    have he := hsource.clean 217 (by decide)
    change a.stacks (FactorTableProgram.basePort (SourceReady.localPort 217)) = [] at he
    have hport : FactorTableProgram.basePort (SourceReady.localPort (217 : Fin 340)) =
        FactorTableProgram.innerPort (217 : Fin 256) := by
      apply Fin.ext
      simp [FactorTableProgram.basePort, SourceReady.localPort, FactorTableProgram.innerPort]
    rw [hport] at he
    simpa only [low, b, FactorTableProgram.projectInner, Function.comp_apply,
      Function.update_of_ne (by decide : FactorTableProgram.innerPort (217 : Fin 256) ≠ 545)]
      using he
  have h857 : b.stacks 857 = s 857 := by
    simp [b, a, sourceCallData, FactorTableProgram.literalReady]
  have ht : b.stacks 881 = [] := by
    simp [b, a, sourceCallData, FactorTableProgram.literalReady, htmp]
  have hhigh (i : Fin 38) :
      b.stacks (FactorTableProgram.joinedPort (QueryProducerSpace.Native.producerPorts i)) = [] := by
    have he := source_high_empty p ps P a j n f S hsource i
    have hne : FactorTableProgram.joinedPort (QueryProducerSpace.Native.producerPorts i) ≠ 545 := by
      intro hi
      have hv := congrArg Fin.val hi
      simp only [FactorTableProgram.joinedPort, QueryProducerSpace.Native.producerPorts,
        Fin.val_natAdd, Fin.coe_ofNat_eq_mod] at hv
      omega
    simpa only [b, Function.update_of_ne hne] using he
  have hshape := FactorTableProgram.joined_shape_of_high_empty b hhigh
  have hencode : b.stacks 857 =
      Squarefree.encodeMask (Squarefree.decodeMask pairs.length (s 857)) := by
    rw [h857, Squarefree.encodeMask_decodeMask pairs.length (s 857) (hmask.trans hpairs.symm)]
  obtain ⟨np, rp, hnp, hgood, hep⟩ :=
    FactorTableProgram.specializeCall_run p.t p.ht p.hd p.model p.modulus p.cache
      u J (p.R+1) hu hJ theta pairs b low hin hz
      (Squarefree.decodeMask pairs.length (s 857)) hencode ht hshape
  refine ⟨xs, hxs, hrows, ns+np, rp, ?_, hgood, hes.seq hep⟩
  rw [h857, hmask] at hnp
  exact Nat.add_le_add hns hnp


/-- The exact generated dictionary fits an ambient-typed Goodempty witness
and one fixed polynomial budget, uniformly over the source's actual row bytes. -/
theorem lowPayload_native_bounded {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f S j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d)
    (s : FactorTableProgram.OuterStore) (acc : List Bool) (regs : Fin 16 → Bool)
    (hcommon : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
      (FactorTableProgram.projectBase s) n)
    (hsource : SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort (sourceCallData s j acc regs)) j n f S)
    (hj : j < n) (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hmask : (s 857).length = n) (htmp : s 881 = []) :
    ∃ (xs : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)))
      (k : ℕ) (rf : Fin 16 → Bool),
      xs.length = n ∧
      LayoutSourceRowsProgram.RowProperty DensePolynomialProgram.Fixed.encode
        (fun z out => PolynomialExecutorProgram.meaning p.ops out.val =
          LayoutSourceRowsProgram.sourceRowFamily ps n f j
            (LayoutSourceRowsProgram.totalPackedSource p P) z)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 xs ∧
      let payload := specializedRowPayload p.t p.model p.modulus p.cache J (p.R+1)
        theta (pairChoice xs (s 546)) (s 857)
      (∃ entries : List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d),
        TruncatedRingProgram.Good ∅ u J entries ∧ payload = MomentsProgram.Product.bytes entries) ∧
      payload.length ≤ specializedPayloadBound n u J (baseWidth 3 p.t) d ∧
      k ≤ Source.nativeSourceWorkPolynomial p S + 1 +
        (7*n+5+specializedWorkPolynomial p.t d u J (p.R+1) n S) ∧
      Eval FactorTableProgram.lowPayload k (sourceCallData s j acc regs)
        (⟨rf,Function.update
          (Function.update (sourceCallData s j acc regs).stacks 545
            (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs))
          557 payload⟩ : FactorTableProgram.OuterData) := by
  obtain ⟨xs,hxs,hrows,k,rf,hk,hgood,he⟩ := lowPayload_native_run p ps P u J n f S j hu hJ
    theta s acc regs hcommon hsource hj hn hf hplans hmask htmp
  let pairs := pairChoice xs (s 546)
  have hchoices : (s 546).length = n := hcommon.choicesLength
  have hpairs : pairs.length = n :=
    (pairChoice_length xs (s 546) (hxs.trans hchoices.symm)).trans hxs
  let words := Encoding.encodeList DensePolynomialProgram.Fixed.encode xs
  let low := FactorTableProgram.projectInner
    (Function.update (sourceCallData s j acc regs).stacks 545 words)
  have hb (i : Fin 256) (hi : i ≠ 205) : (low i).length ≤ S :=
    source_output_cache_bound (sourceCallData s j acc regs) words S hsource.size i hi
  have hraw := emittedSource_bytes_bound p.t p.ht p.hd p.model p.modulus p.cache
    u J (p.R+1) hu hJ theta pairs
  have hbudget := specializeBudget_le p.t d u J (p.R+1) pairs.length S _ low
    (hb 192 (by decide)) (hb 193 (by decide)) (hb 243 (by decide))
    (hb 194 (by decide)) (hb 202 (by decide)) (hb 204 (by decide)) hraw
  have hbudget' := hbudget.trans_eq
    (congrArg (fun m => specializedWorkPolynomial p.t d u J (p.R+1) m S) hpairs)
  have hlen := TruncatedRingProgram.empty_bytes_length_le hgood
  have hlen' := hlen.trans_eq (congrArg
    (fun m => u*J*(2*(u+J+m)+2*(d*baseWidth 3 p.t)+2)) hpairs)
  refine ⟨xs,k,rf,hxs,hrows,?_,hlen',?_,he⟩
  · exact good_bytes_transport hpairs _ hgood
  · exact hk.trans (Nat.add_le_add_left (Nat.add_le_add_left hbudget' _) _)


def specializedLiteralWork {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (u J n S H : ℕ) : ℕ :=
  7*n + (10*n+9*H+18+(10*n+42*n+29*(d*baseWidth 3 p.t)+109)+
    (Source.nativeSourceWorkPolynomial p S+1+
      (7*n+5+specializedWorkPolynomial p.t d u J (p.R+1) n S))) +
    22*(n+1)+19*specializedPayloadBound n u J (baseWidth 3 p.t) d+
    2*(n*(2*((p.R+1)*(d*baseWidth 3 p.t))+2)+1)+54

/-- Every literal branch is discharged by the actual fixed source and
immediate normalizer. Its source assumption contains physical words only. -/
theorem native_literal {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f S j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d)
    (s : FactorTableProgram.OuterStore) (acc : List Bool)
    (h : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
      (FactorTableProgram.projectBase s) n)
    (hsource : ∀ regs : Fin 16 → Bool, SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort (sourceCallData s j acc regs)) j n f S)
    (hj : j < n) (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (h545 : s 545 = []) (h555 : s 555 = []) (h557 : s 557 = [])
    (hm : (s 575).length = n) (hmask : (s 857).length = n) (htmp : s 881 = [])
    (regs : Fin 16 → Bool) :
    ∃ payload k rf, k ≤ specializedLiteralWork p u J n S (s 574).length ∧
      payload.length ≤ specializedPayloadBound n u J (baseWidth 3 p.t) d ∧
      PayloadMeaning p ps P u J n f theta s j payload ∧
      Eval FactorTableProgram.literalIteration k
        (⟨regs,FactorTableProgram.literalReady s (List.replicate j true) acc⟩ : FactorTableProgram.OuterData)
        (⟨rf,FactorTableProgram.literalReady s (List.replicate j true)
          (Encoding.frame (Encoding.encodeNat j)++Encoding.frame payload++acc)⟩ : FactorTableProgram.OuterData) := by
  let current := FactorTableProgram.literalReady s (List.replicate j true) acc
  let keyed := Function.update current 555 (Encoding.encodeNat j)
  let W := d*baseWidth 3 p.t
  let Lrows := n*(2*((p.R+1)*W)+2)+1
  let Lpayload := specializedPayloadBound n u J (baseWidth 3 p.t) d
  let Klow := Source.nativeSourceWorkPolynomial p S+1+
    (7*n+5+specializedWorkPolynomial p.t d u J (p.R+1) n S)
  let Kpayload := 10*j+9*(s 574).length+18+(10*j+42*n+29*W+109)+Klow
  have scratch (i : Fin 256) (hi : i ∈ lowScratch) :
      s (FactorTableProgram.innerPort i) = [] := by
    have hh := h.scratch i hi
    change s (FactorTableProgram.basePort (PerturbationAssembly.innerPort i)) = [] at hh
    rwa [FactorTableProgram.basePort_inner] at hh
  have he : ∀ i∈entryScratch,current (FactorTableProgram.innerPort i)=[] := by
    intro i hi
    have hni : FactorTableProgram.innerPort i≠573 ∧ FactorTableProgram.innerPort i≠569 := by
      simp only [entryScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hilow : i ∈ lowScratch := by
      simp only [entryScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [current,FactorTableProgram.literalReady,Function.update_apply,hni.1,hni.2] using
      scratch i hilow
  have ho : ∀ i∈originScratch,keyed (FactorTableProgram.innerPort i)=[] := by
    intro i hi
    have hni : FactorTableProgram.innerPort i≠573 ∧ FactorTableProgram.innerPort i≠569 ∧
        FactorTableProgram.innerPort i≠555 := by
      simp only [originScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hilow : i ∈ lowScratch := by
      simp only [originScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [keyed,current,FactorTableProgram.literalReady,Function.update_apply,hni.1,hni.2.1,hni.2.2] using
      scratch i hilow
  have h220 : keyed 560=[] := by
    simpa [keyed,current,FactorTableProgram.literalReady,FactorTableProgram.innerPort] using scratch 220 (by decide)
  have hz : (keyed 547).length=W := by
    simpa [keyed,current,FactorTableProgram.literalReady,W,FactorTableProgram.projectBase,
      FactorTableProgram.basePort] using congrArg List.length h.zeroWord
  have h1 : (keyed 548).length=W := by
    simpa [keyed,current,FactorTableProgram.literalReady,W,FactorTableProgram.projectBase,
      FactorTableProgram.basePort] using congrArg List.length h.oneWord
  have hprogram : p.ops.program =
      RingProgram.modelProgram p.t p.model p.modulus p.cache := by
    exact RingProgram.modelRing_program p.t p.ht p.hd p.model p.modulus p.cache
  have hzeroRun := congrArg (fun q => q.zeroRun) hprogram
  have honeRun := congrArg (fun q => q.oneRun) hprogram
  have hzeroRun' : p.ops.zeroRun =
      (RingProgram.modelProgram p.t p.model p.modulus p.cache).zeroRun := by
    simpa only [SubexpSymbolicCost.RepresentedRing.program] using hzeroRun
  have honeRun' : p.ops.oneRun =
      (RingProgram.modelProgram p.t p.model p.modulus p.cache).oneRun := by
    simpa only [SubexpSymbolicCost.RepresentedRing.program] using honeRun
  have hzWord : keyed 547=RingProgram.flat p.ops.zeroRun.1 := by
    rw [hzeroRun']
    simpa [keyed,current,FactorTableProgram.literalReady,FactorTableProgram.projectBase,
      FactorTableProgram.basePort] using h.zeroWord
  have h1Word : keyed 548=RingProgram.flat p.ops.oneRun.1 := by
    rw [honeRun']
    simpa [keyed,current,FactorTableProgram.literalReady,FactorTableProgram.projectBase,
      FactorTableProgram.basePort] using h.oneWord
  have hhighGood : ∃ entries : List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d),
      TruncatedRingProgram.Good ∅ u J entries ∧
      Encoding.frame (originKey n) ++
        Encoding.frame (if (keyed 575).getD (keyed 573).length false then keyed 548 else keyed 547) =
        MomentsProgram.Product.bytes entries := by
    cases hb : (keyed 575).getD (keyed 573).length false
    · simp only [Bool.false_eq_true, ite_false, hzWord]
      exact FactorTableProgram.high_payload_good (n:=n) u J hu hJ p.ops.zeroRun.1
    · simp only [ite_true, h1Word]
      exact FactorTableProgram.high_payload_good (n:=n) u J hu hJ p.ops.oneRun.1
  have hp : ∀ rs : Fin 16 → Bool, ∃ words payload k rf, k≤Kpayload ∧
      words.length≤Lrows ∧ payload.length≤Lpayload ∧
      PayloadMeaning p ps P u J n f theta s j payload ∧
      Eval FactorTableProgram.literalPayload k (⟨rs,keyed⟩ : FactorTableProgram.OuterData)
        (⟨rf,Function.update (Function.update keyed 545 words) 557 payload⟩ : FactorTableProgram.OuterData) := by
    intro rs
    suffices hs : ∃ words payload k rf,
        k≤10*(keyed 573).length+9*(keyed 574).length+18+
          (10*(keyed 573).length+42*n+29*W+109)+Klow ∧
        words.length≤Lrows ∧ payload.length≤Lpayload ∧
        PayloadMeaning p ps P u J n f theta s j payload ∧
        Eval FactorTableProgram.literalPayload k (⟨rs,keyed⟩ : FactorTableProgram.OuterData)
          (⟨rf,Function.update (Function.update keyed 545 words) 557 payload⟩ : FactorTableProgram.OuterData) by
      simpa [Kpayload,keyed,current,FactorTableProgram.literalReady] using hs
    refine FactorTableProgram.literalPayload_rel keyed n W Klow Lrows Lpayload
      (PayloadMeaning p ps P u J n f theta s j)
      (by simpa [keyed,current,FactorTableProgram.literalReady,FactorTableProgram.projectBase,
        FactorTableProgram.basePort] using congrArg List.length h.ambientCount)
      (by simpa [keyed,current,FactorTableProgram.literalReady] using hm) hz h1
      (by simpa [keyed,current,FactorTableProgram.literalReady] using h545)
      (by simpa [keyed,current,FactorTableProgram.literalReady] using h557) h220 ho ?_ ?_ ?_ rs
    · intro hb rs'
      have hb' : (s 574).getD j false=false := by
        simpa [keyed,current,FactorTableProgram.literalReady] using hb
      obtain ⟨xs,k,rf,hxs,hrows,hgood,hlen,hk,hev⟩ :=
        lowPayload_native_bounded p ps P u J n f S j hu hJ theta s acc rs' h
          (hsource rs') hj hn hf hplans hmask htmp
      refine ⟨Encoding.encodeList DensePolynomialProgram.Fixed.encode xs,
        specializedRowPayload p.t p.model p.modulus p.cache J (p.R+1) theta
          (pairChoice xs (s 546)) (s 857),k,rf,hk,?_,hlen,⟨hgood,?_⟩,hev⟩
      · have hl := sourceWords_length (pairChoice xs (s 546))
        have hc : xs.length=(s 546).length := hxs.trans h.choicesLength.symm
        simpa [sourceWords,pairChoice_rows xs (s 546) hc,pairChoice_length xs (s 546) hc,
          hxs,Lrows,W] using hl.le
      · simp only [hb',Bool.false_eq_true,ite_false]
        exact ⟨xs,hxs,hrows,rfl⟩
    · intro hb
      refine ⟨hhighGood,?_⟩
      have hb' : (s 574).getD j false=true := by
        simpa [keyed,current,FactorTableProgram.literalReady] using hb
      simp only [hb',ite_true]
      simp [keyed,current,FactorTableProgram.literalReady]
    · obtain ⟨entries,hgood,hbytes⟩ := hhighGood
      rw [hbytes]
      exact TruncatedRingProgram.empty_bytes_length_le hgood
  obtain ⟨payload,k,rf,hk,hlen,hmeaning,heval⟩ := FactorTableProgram.literalIteration_rel current j
    Kpayload Lrows Lpayload (PayloadMeaning p ps P u J n f theta s j)
    (by simp [current,FactorTableProgram.literalReady])
    (by simpa [current,FactorTableProgram.literalReady] using h545)
    (by simpa [current,FactorTableProgram.literalReady] using h555)
    (by simpa [current,FactorTableProgram.literalReady] using h557) he hp regs
  refine ⟨payload,k,rf,?_,hlen,hmeaning,?_⟩
  · dsimp only [Kpayload,Klow,Lpayload,Lrows,W] at hk
    unfold specializedLiteralWork
    omega
  · simpa [current,FactorTableProgram.literalReady,List.append_assoc] using heval


/-- The physical source invariant is reused at every ambient ID, while its
size covers the actual cursor, encoded key and retained specialized table. -/
theorem native_literal_body {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f S B : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (a : FactorTableProgram.OuterData)
    (h : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
      (FactorTableProgram.projectBase a.stacks) n)
    (hsource : SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort a) 0 n f S)
    (hbase : ∀ i, (a.stacks i).length ≤ B)
    (hsize : B+n+n*FactorTableProgram.literalRecordBound n
      (specializedPayloadBound n u J (baseWidth 3 p.t) d)+1 ≤ S)
    (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (h545 : a.stacks 545 = []) (h555 : a.stacks 555 = []) (h557 : a.stacks 557 = [])
    (hm : (a.stacks 575).length = n) (hmask : (a.stacks 857).length = n)
    (htmp : a.stacks 881 = []) :
    FactorTableProgram.RelLiteralBody a.stacks FactorTableProgram.literalIteration
      (PayloadMeaning p ps P u J n f theta a.stacks)
      (specializedLiteralWork p u J n S (a.stacks 574).length) n
      (specializedPayloadBound n u J (baseWidth 3 p.t) d) := by
  constructor
  intro j hj acc hacc regs
  apply native_literal p ps P u J n f S j hu hJ theta a.stacks acc h
  · intro rs
    apply sourceInput_at_call p ps P a 0 n f S j acc rs hsource
    intro i
    exact (sourceCallData_wordBound a.stacks B n _ j acc rs hbase hj hacc i).trans hsize
  · exact hj
  · exact hn
  · exact hf
  · exact hplans
  · exact h545
  · exact h555
  · exact h557
  · exact hm
  · exact hmask
  · exact htmp

/-- Only concrete retained words and numeric size bounds occur in the table
entry contract. Private scratch is cleared and rebuilt by the command itself. -/
structure Ready {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f B S : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (a : FactorTableProgram.OuterData) : Prop where
  positiveU : 0 < u
  positiveJ : 0 < J
  scalar : ScalarMasters p.t p.model p.modulus p.cache J p.R theta
    (projectState id FactorTableProgram.basePort a) n
  masters : SourceMasters p ps P (projectState id FactorTableProgram.basePort a)
  selected : a.stacks 556 = List.replicate f true
  mask : (a.stacks 857).length = n
  incoming : ∀ i, (a.stacks i).length ≤ B
  size : 1029*B+99+n+n*FactorTableProgram.literalRecordBound n
    (specializedPayloadBound n u J (baseWidth 3 p.t) d)+1 ≤ S
  arraySize : (p.R+1)*(d*baseWidth 3 p.t) ≤ S
  countSize : p.R+1 ≤ S
  metadataSize : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S
  incidenceSize : ps.length ≤ S
  ambientSize : n ≤ S
  factorSize : f ≤ S
  plansSize : (LayoutOwnerFiberProgram.stream ps).length ≤ S

/-- Actual retained words discharge the source's per-entry size requirements.
The metadata bound follows from physical lookup serialization, and the
incidence count follows from the actual addressed plan stream. -/
theorem Ready.of_masters {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (hu : 0 < u) (hJ : 0 < J)
    (hscalar : ScalarMasters p.t p.model p.modulus p.cache J p.R theta
      (projectState id FactorTableProgram.basePort a) n)
    (hmasters : SourceMasters p ps P (projectState id FactorTableProgram.basePort a))
    (hselected : a.stacks 556 = List.replicate f true)
    (hmask : (a.stacks 857).length = n)
    (hincoming : ∀ i, (a.stacks i).length ≤ B)
    (hsize : 1029*B+99+n+n*FactorTableProgram.literalRecordBound n
      (specializedPayloadBound n u J (baseWidth 3 p.t) d)+1 ≤ S)
    (hRQ : p.R+1 ≤ Q) : Ready p ps P u J n f B S theta a := by
  have hBS : B ≤ S := by omega
  have hcap (i : Fin 768) :
      ((projectState id FactorTableProgram.basePort a).stacks i).length ≤ B :=
    hincoming (FactorTableProgram.basePort i)
  have hrow := hcap 716
  rw [hmasters.rowWidth,p.hrowWidth,p.hringWidth] at hrow
  have hnodes := hcap 131
  rw [hmasters.nodes,List.length_replicate] at hnodes
  have hmetadata := hcap 135
  rw [hmasters.metadata] at hmetadata
  have hplans := hcap 136
  rw [hmasters.plans] at hplans
  have hincidence : ps.length ≤ B := by
    have hlength := LayoutOwnerFiberProgram.stream_length ps
    omega
  have hn := hincoming 857
  rw [hmask] at hn
  have hf := hincoming 556
  rw [hselected,List.length_replicate] at hf
  refine ⟨hu,hJ,hscalar,hmasters,hselected,hmask,hincoming,hsize,
    ((Nat.mul_le_mul_right _ hRQ).trans hrow).trans hBS,
    (hRQ.trans hnodes).trans hBS,?_,hincidence.trans hBS,hn.trans hBS,
    hf.trans hBS,hplans.trans hBS⟩
  intro x
  have hinj : Function.Injective (fun v : Fin ps.length => List.replicate v.val true) := by
    intro v w he
    apply Fin.ext
    simpa only [List.length_replicate] using congrArg List.length he
  have hl := PackingMetadata.lookup_eq P (fun v => List.replicate v.val true)
    CollisionProgram.encodeType hinj x
  have hp := ((GlobalBasisMetadata.payload_length_le _ _ _ hl).trans hmetadata).trans hBS
  have hb (m : GlobalBasisMetadata.Metadata) :
      m.block.length ≤ m.encode.length ∧ m.typeCode.length ≤ m.encode.length ∧
        m.rank.length ≤ m.encode.length := by
    cases m <;> simp [GlobalBasisMetadata.Metadata.block,GlobalBasisMetadata.Metadata.typeCode,
      GlobalBasisMetadata.Metadata.rank,GlobalBasisMetadata.Metadata.encode,Encoding.length_frame] <;> omega
  exact ⟨(hb _).1.trans hp,(hb _).2.1.trans hp,(hb _).2.2.trans hp⟩

theorem Ready.staged_common {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (h : Ready p ps P u J n f B S theta a) :
    StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
      (FactorTableProgram.projectBase (FactorTableProgram.staged a).stacks) n := by
  have hh := (h.scalar.initialized a).staged
  have he := congrArg StructuredProgram.State.stacks (project_staged a)
  change FactorTableProgram.projectBase (FactorTableProgram.staged a).stacks = _ at he
  rw [he]
  exact hh

theorem Ready.staged_empty {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (h : Ready p ps P u J n f B S theta a) (i : Fin 768)
    (hi : i ∈ ([460,545,555,557,561,569,573,585] : List (Fin 768))) :
    (FactorTableProgram.staged a).stacks (FactorTableProgram.basePort i) = [] := by
  have hh := (h.scalar.initialized a).staged_empty i hi
  have he := congrArg (fun b : SourceReady.Data => b.stacks i) (project_staged a)
  exact he.trans hh

theorem Ready.staged_high {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (h : Ready p ps P u J n f B S theta a) :
    ((FactorTableProgram.staged a).stacks 575).length = n := by
  have hh := (h.scalar.initialized a).staged_high
  have he := congrArg (fun b : SourceReady.Data => (b.stacks 575).length) (project_staged a)
  exact he.trans hh

theorem staged_mask (a : FactorTableProgram.OuterData) :
    (FactorTableProgram.staged a).stacks 857 = a.stacks 857 :=
  FactorTableSpace.staged_frame a 857
    (FactorTableSpace.caller_port_not_written 857 (Or.inr (Or.inr (by decide))))

theorem staged_mask_scratch (a : FactorTableProgram.OuterData) :
    (FactorTableProgram.staged a).stacks 881 = [] := by
  change (embedState id FactorTableProgram.basePort (FactorTableProgram.initialized a) _).stacks 881 = []
  rw [embedState_stack_frame _ _ _ _ 881
    (FactorTableProgram.basePort_outside 881 (Or.inr (by decide)))]
  rw [FactorTableProgram.initialized,clearMany_stacks,ite_eq_left]
  exact List.mem_append_right _ (by simp)

theorem Ready.body {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (h : Ready p ps P u J n f B S theta a) :
    FactorTableProgram.RelLiteralBody (FactorTableProgram.staged a).stacks FactorTableProgram.literalIteration
      (PayloadMeaning p ps P u J n f theta (FactorTableProgram.staged a).stacks)
      (specializedLiteralWork p u J n S ((FactorTableProgram.staged a).stacks 574).length) n
      (specializedPayloadBound n u J (baseWidth 3 p.t) d) := by
  apply native_literal_body p ps P u J n f S (1029*B+99) h.positiveU h.positiveJ theta
    (FactorTableProgram.staged a) h.staged_common
  · exact source_of_masters p ps P a theta h.scalar h.masters h.selected h.incoming
      (by have := h.size; omega) h.arraySize h.countSize h.metadataSize h.incidenceSize
  · exact FactorTableSpace.staged_stack_bound a B h.incoming
  · exact h.size
  · exact h.ambientSize
  · exact h.factorSize
  · exact h.plansSize
  · exact h.staged_empty 545 (by simp)
  · exact h.staged_empty 555 (by simp)
  · exact h.staged_empty 557 (by simp)
  · exact h.staged_high
  · rw [staged_mask]; exact h.mask
  · exact staged_mask_scratch a

/-- The table entry contract discharges every literal execution. The output
is the exact attained native family, with scalar Goodempty dictionaries,
full original-variable lookup format, time, and all-prefix source space on
one and the same fixed finite program run. -/
theorem command_native_resources {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (h : Ready p ps P u J n f B S theta a) :
    let K := specializedLiteralWork p u J n S ((FactorTableProgram.staged a).stacks 574).length
    let L := specializedPayloadBound n u J (baseWidth 3 p.t) d
    ∃ (incidence : Fin n → List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d))
      (steps : ℕ) (e : FactorTableProgram.OuterData),
      (∀ v, TruncatedRingProgram.Good ∅ u J (incidence v)) ∧
      (∀ v, (MomentsProgram.Product.bytes (incidence v)).length ≤ L) ∧
      (∀ v, PayloadMeaning p ps P u J n f theta (FactorTableProgram.staged a).stacks
        v.val (MomentsProgram.Product.bytes (incidence v))) ∧
      steps ≤ FactorTableSpace.commandBudget B n K L ∧
      Trace FactorTableProgram.program steps (a.withPC (some FactorTableProgram.program.entry)) (e.withPC none) ∧
      e.stacks 62 = Squarefree.Program.lookupRecords
        (HashCircuitProgram.incidenceEntries (fun (_ : Unit) v => MomentsProgram.Product.bytes (incidence v)) ()) ∧
      (∀ i, i ∉ FactorTableSpace.writtenPorts → e.stacks i = a.stacks i) ∧
      (∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → e.stacks i = []) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace FactorTableProgram.program prefixSteps (a.withPC (some FactorTableProgram.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896*B+FactorTableSpace.commandBudget B n K L := by
  classical
  dsimp only
  obtain ⟨payload,steps,e,hpayload,hsteps,htrace,houtput,hframe,hclean,hprefix⟩ :=
    FactorTableSpace.command_resources a B n _ _ h.incoming h.staged_common.ambientCount
      (h.staged_empty 460 (by simp)) (h.staged_empty 573 (by simp))
      (h.staged_empty 569 (by simp)) (h.staged_empty 561 (by simp))
      (h.staged_empty 585 (by simp)) _ h.body
  have hw (v : Fin n) := (hpayload v.val v.isLt).2.good
  choose incidence hgood hbytes using hw
  refine ⟨incidence,steps,e,hgood,?_,?_,hsteps,htrace,?_,hframe,hclean,hprefix⟩
  · intro v
    rw [← hbytes v]
    exact (hpayload v.val v.isLt).1
  · intro v
    rw [← hbytes v]
    exact (hpayload v.val v.isLt).2
  · rw [houtput,FactorTableProgram.tableResult_incidence]
    have hf : (fun (_ : Unit) (v : Fin n) => payload v.val) =
        (fun (_ : Unit) (v : Fin n) => MomentsProgram.Product.bytes (incidence v)) := by
      funext x v
      exact hbytes v
    rw [hf]


/-- Returned cleanliness and the off-port frame identify the whole store,
not just a selected output tape. The selected factor ID is consumed. -/
theorem restored_stacks (a e : FactorTableProgram.OuterData) (bytes : List Bool)
    (hout : e.stacks 62 = bytes)
    (hframe : ∀ i, i ∉ FactorTableSpace.writtenPorts → e.stacks i = a.stacks i)
    (hclean : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → e.stacks i = [])
    (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = []) :
    e.stacks = Function.update (Function.update a.stacks 556 []) 62 bytes := by
  funext i
  by_cases h62 : i = 62
  · subst i
    simpa only [Function.update_self] using hout
  by_cases h556 : i = 556
  · subst i
    have hm : (556 : Fin 896) ∈ FactorTableSpace.writtenPorts := by
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨556,
        (Incidence.mem_workerPorts 556).mpr (by decide), rfl⟩
    simpa only [Function.update_of_ne h62,Function.update_self] using hclean 556 hm h62
  rw [Function.update_of_ne h62,Function.update_of_ne h556]
  by_cases hm : i ∈ FactorTableSpace.writtenPorts
  · rw [hclean i hm h62,hblank i hm h62 h556]
  · exact hframe i hm

theorem callerRegisters_injective : Function.Injective FactorTableProgram.callerRegisters := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  exact hv

/-- The actual fixed40-register caller exports the same typed dictionaries,
consumes only factor556, restores the remaining initially blank private bank,
and frames all registers outside its16-register instruction table. -/
theorem caller_native_resources {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} (a : State 40 896)
    (h : Ready p ps P u J n f B S theta
      (projectState FactorTableProgram.callerRegisters id a))
    (hblank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = []) :
    let localInput := projectState FactorTableProgram.callerRegisters id a
    let K := specializedLiteralWork p u J n S ((FactorTableProgram.staged localInput).stacks 574).length
    let L := specializedPayloadBound n u J (baseWidth 3 p.t) d
    ∃ (incidence : Fin n → List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d))
      (steps : ℕ) (e : State 40 896),
      (∀ v, TruncatedRingProgram.Good ∅ u J (incidence v)) ∧
      (∀ v, (MomentsProgram.Product.bytes (incidence v)).length ≤ L) ∧
      (∀ v, PayloadMeaning p ps P u J n f theta (FactorTableProgram.staged localInput).stacks
        v.val (MomentsProgram.Product.bytes (incidence v))) ∧
      steps ≤ FactorTableSpace.commandBudget B n K L ∧
      Eval FactorTableProgram.caller steps a e ∧
      e.stacks = Function.update (Function.update a.stacks 556 []) 62
        (Squarefree.Program.lookupRecords (HashCircuitProgram.incidenceEntries
          (fun (_ : Unit) v => MomentsProgram.Product.bytes (incidence v)) ())) ∧
      (∀ i : Fin 40, 16 ≤ i.val → e.regs i = a.regs i) ∧
      Trace (compiled FactorTableProgram.caller 556 62) (steps+1)
        (a.withPC (some (compiled FactorTableProgram.caller 556 62).entry)) (e.withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps+1 →
        Trace (compiled FactorTableProgram.caller 556 62) prefixSteps
          (a.withPC (some (compiled FactorTableProgram.caller 556 62).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896*B+FactorTableSpace.commandBudget B n K L+1 := by
  dsimp only
  obtain ⟨incidence,steps,b,hgood,hlen,hmeaning,hsteps,htrace,hout,hframe,hclean,_⟩ :=
    command_native_resources h
  let e := embedState FactorTableProgram.callerRegisters id a b
  have he : Eval FactorTableProgram.caller steps a e :=
    eval_call_from_state FactorTableProgram.program FactorTableProgram.callerRegisters id a
      callerRegisters_injective Function.injective_id htrace
  have hs : e.stacks=b.stacks := by
    funext i
    exact embedState_stack _ _ _ _ Function.injective_id i
  have hstore := restored_stacks (projectState FactorTableProgram.callerRegisters id a) b _
    hout hframe hclean hblank
  have hrun := compiled_halt_trace he 556 62
  refine ⟨incidence,steps,e,hgood,hlen,hmeaning,hsteps,he,?_,?_,hrun,?_⟩
  · rw [hs,hstore]
    rfl
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    have hlt := j.isLt
    change j.val=i.val at hv
    omega
  · intro prefixSteps intermediate hp ht i
    have hb : ∀ i, (a.stacks i).length ≤ B := h.incoming
    have hbound := StructuredSpace.local_stack_bound
      (compiled FactorTableProgram.caller 556 62)
      (StreamResources.dataBits_le_mul _ hb) prefixSteps intermediate
      (hp.trans (Nat.add_le_add_right hsteps 1)) ht i
    simpa only [Nat.add_assoc] using hbound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
