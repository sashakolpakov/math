import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankCache

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open RowSelectionProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

private theorem zero_cleanup (a : Data) (h : MetadataReady a)
    (hp : a.stacks 254=[]) (hn : a.stacks 255=[]) :
    Eval cleanup (Staging.cost 0 1 cleanupOps a) a
      (finish a (Staging.result 0 1 cleanupOps a).regs ([],[])) := by
  have he := cleanup_eval a (h 199 (by decide) (Or.inr (by decide)))
  have hh : Staging.result 0 1 cleanupOps a=
      finish a (Staging.result 0 1 cleanupOps a).regs ([],[]) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext j
      calc
        (Staging.result 0 1 cleanupOps a).stacks j =
            if j.val < 200 then [] else a.stacks j := cleanup_stacks a j
        _ = (finish a (Staging.result 0 1 cleanupOps a).regs ([],[])).stacks j := by
          by_cases h255 : j=255
          · subst j; simp [finish,hn]
          · by_cases h254 : j=254
            · subst j; simp [finish,hp]
            · simp [finish,h255,h254]
  rw [hh] at he
  exact he

/-- No arithmetic is run when the selected row is covered and the selected
column is outside the covered blocks. Metadata cleanup is still charged. -/
theorem covered_uncovered_eval (a : Data) (h : MetadataReady a)
    (hp : a.stacks 254=[]) (hn : a.stacks 255=[])
    (h5 : a.regs 5=false) :
    ∃ n ≤ 2*metadataFieldsLength a+601, ∃ rf,
      Eval (.seq covered cleanup) n a (finish a rf ([],[])) := by
  have hc := cleanup_metadata_cost a h
  refine ⟨1+Staging.cost 0 1 cleanupOps a,by omega,
    (Staging.result 0 1 cleanupOps a).regs,?_⟩
  exact (Eval.ite_false (yes:=.seq compareBlocks (.ite 7
    (.seq prepare (.seq integer exportPair)) (.base .skip))) h5
    (Eval.base (StructuredProgram.Eval.skip a))).seq (zero_cleanup a h hp hn)

/-- Both metadata records are covered: an actual comparison chooses the
cached universal entry or literal zero. The private caller bank is retained. -/
theorem covered_eval (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q) (u y : UniversalType r Q 1)
    (a : Data) (S K L : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : CacheWords (r:=r) a (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
    (hready : MetadataReady a) (h254 : a.stacks 254=[]) (h255 : a.stacks 255=[])
    (hu : a.stacks 65=CollisionProgram.encodeType u) (hy : a.stacks 68=CollisionProgram.encodeType y)
    (h5 : a.regs 5=true)
    (hsize : ∀ j : Fin 256, j.val < 212 → (a.stacks j).length ≤ S)
    (hK : IntegerEntry.budget aWord.length R width.length (pairLength power) power.1.length t u y ≤ K)
    (hL : IntegerEntry.lengthBound R width.length (pairLength power) u y+power.1.length+1 ≤ L) :
    ∃ n ≤ K+511*S+407*L+1107, ∃ rf result,
      Eval (.seq covered cleanup) n a (finish a rf result) ∧
      pairValue result=(if a.stacks 64=a.stacks 67 then IntegerEntry.value aWord.length R t u y else 0) ∧
      LayoutProgramScalar.wordTotal result ≤ constraintMassBound Q R ∧ pairLength result ≤ L := by
  obtain ⟨nc,hnc,b,hcompare,hbs,_,h7⟩ := compareBlocks_eval a
    (fun j hj => hready j (by omega) (Or.inl (by omega)))
  have hcmp : nc ≤ 27*S+32 := by
    have h1 := hsize 64 (by decide)
    have h2 := hsize 67 (by decide)
    omega
  have hbready : MetadataReady b := by intro j hj hk; rw [hbs]; exact hready j hj hk
  have hb254 : b.stacks 254=[] := by rw [hbs]; exact h254
  have hb255 : b.stacks 255=[] := by rw [hbs]; exact h255
  have hbframe : ∀ j : Fin 256,200 ≤ j.val → b.stacks j=a.stacks j := by intro j _; rw [hbs]
  have hbsize : ∀ j : Fin 256,j.val < 212 → (b.stacks j).length ≤ S := by
    intro j hj; rw [hbs]; exact hsize j hj
  by_cases heq : a.stacks 64=a.stacks 67
  · have hbc : Cached b (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t u y :=
      (hc.frame hbframe).cached u y hbready hb254 hb255 (by rw [hbs]; exact hu) (by rw [hbs]; exact hy)
    obtain ⟨ni,hni,rf,result,hi,hv,hm,hl⟩ := inner_eval Hwords width power aWord R t u y b S
      hlen hwords hvalues hp hpt hpos hwidth hAQ hQ hbc hbsize
    have hh := covered_attach hcompare h5 (show b.regs 7=true by simp [h7,heq]) hi
    rw [finish_frame rf result hbframe] at hh
    refine ⟨nc+ni+2,by omega,rf,result,hh,?_,hm,hl.trans hL⟩
    simpa only [ite_eq_left heq] using hv
  · have ht := zero_cleanup b hbready hb254 hb255
    have hbranch := Eval.ite_true (no := (.base .skip : Code)) h5
      (hcompare.seq (Eval.ite_false (yes := .seq prepare (.seq integer exportPair))
        (show b.regs 7=false by simp [h7,heq]) (Eval.base (StructuredProgram.Eval.skip b))))
    have hh := hbranch.seq ht
    rw [finish_frame (Staging.result 0 1 cleanupOps b).regs ([],[]) hbframe] at hh
    have hclean := cleanup_metadata_cost b hbready
    have hfields := metadata_fields_le hbsize
    refine ⟨nc+2+Staging.cost 0 1 cleanupOps b,by omega,
      (Staging.result 0 1 cleanupOps b).regs,([],[]),?_,?_,?_,?_⟩
    · have htime : nc+2+Staging.cost 0 1 cleanupOps b =
          nc+(0+1)+1+Staging.cost 0 1 cleanupOps b := by omega
      rw [htime]
      exact hh
    · simp [heq,pairValue,RowSelectionProgram.signedValue]
    · simp [LayoutProgramScalar.wordTotal,pairTotal]
    · simp [pairLength]

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
