import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.NodePreludeSum
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCostAssembly
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheTyped

namespace OAI.Algorithms

/-! Replace the combined node scale by original input words. Only the
27 master ports actually read by the residual bounds are counted: the
moment and query streams on 127 and 25 are deliberately absent. -/
namespace SubexponentialSAT.Subexp.NodeCanonicalScale

open scoped BigOperators
open SubexpNodeWorkspace SubexpNodeStoreTransitions SubexpNodeContexts
open SubexpLiftRing ConstructivePacking

abbrev Bits := List Bool
abbrev Data := StructuredProgram.State 16 288

def masterPorts : Finset (Fin 288) :=
  {5,10,91,121,122,123,124,126,128,129,130,131,255,258,261,264,
    266,269,270,271,272,276,277,279,280,282,283}

def masterVolume (masters : Store) : ℕ := ∑ i ∈ masterPorts, (masters i).length

theorem master_le (masters : Store) (i : Fin 288) (hi : i∈masterPorts) :
    (masters i).length ≤ masterVolume masters := by
  unfold masterVolume
  exact Finset.single_le_sum (s := masterPorts)
    (f := fun j : Fin 288 => (masters j).length)
    (fun j _ => Nat.zero_le (masters j).length) hi

private theorem read_sum_le (masters : Store) (S : ℕ)
    (h : ∀ i∈masterPorts, (masters i).length ≤ S) (xs : List (Fin 288))
    (hx : xs.toFinset⊆masterPorts) :
    (xs.map (fun i => (masters i).length)).sum ≤ xs.length*S := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
      have hi := h i (hx (by simp))
      have ht := ih (by intro j hj; exact hx (by simp only [List.toFinset_cons,Finset.mem_insert]; exact Or.inr hj))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

/-- All terms are original masters, numerical parameters, or explicitly
provided input words. No generated Taylor cache or template occurs. -/
def originalSize (p D R r Q m : ℕ) (masters : Store)
    (node query index : Bits) (nodes : List Bits) (modulus zero one : Bits)
    (scopes : List (List ℕ)) (tables : List Bits) (scalarCache : List (List Bits)) : ℕ :=
  masterVolume masters +
    NodeCacheBounds.scale m D R (R+1) (baseWidth p (D+1)) (baseWidth p 1) modulus.length +
    p+r+Q+SubexpSymbolicCost.indexBits D + node.length+query.length+index.length+
    (ProgramEncoding.encodeRecords nodes).length +
    (Encoding.encodeList SubexpFactorPrefixProgram.scopeBytes scopes).length +
    (Encoding.encodeList id tables).length + (FactorPacketCoordinates.cacheBytes scalarCache).length +
    modulus.length+zero.length+one.length+1

private theorem basis_volume_eq (masters : Store) (node cache index : Bits)
    (d : Data) (hd : d.stacks=indexed masters node cache index) :
    SubexpNodeBasisExecution.inputVolume d = index.length+
      ([269,266,261,264,270,271,272,276,282,283].map
        (fun i : Fin 288 => (masters i).length)).sum := by
  simp [SubexpNodeBasisExecution.inputVolume,SubexpNodeBasisStage.moves,hd,
    indexed,cached,activeStacks,initialStacks,MasterPort,Fin.coe_ofNat_eq_mod]

section Bound

variable (p D R r Q Δ m : ℕ) [Fact p.Prime]
variable (masters : Store) (node query index : Bits) (nodes : List Bits)
variable (modulus zero one : Bits) (scopes : List (List ℕ)) (tables : List Bits)
variable (scalarCache : List (List Bits))

local notation "K" => NodeCacheBounds.scale m D R (R+1)
  (baseWidth p (D+1)) (baseWidth p 1) modulus.length
local notation "PS" => SubexpNodePacketInputBound.staticSize p (D+1) R (R+1) D m
  modulus zero one scopes tables scalarCache
local notation "OS" => originalSize p D R r Q m masters node query index nodes
  modulus zero one scopes tables scalarCache

/-- Canonical-state substitution removes every generated cache/template
size from the combined prelude, packet and suffix scale. The only cache
premise is its exact equality to the actual Taylor-map output. -/
theorem combinedScale_le
    (packing : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Bits)
    (M : SubexpPreparedQuartic.Modulus p (D+1))
    (reduction theta : SubexpTaylorRow.Code p (D+1))
    (rows : List (List (List (SubexpTaylorRow.Code p (D+1)))))
    (hm : rows.length ≤ m) (hD : ∀ coordinates∈rows, coordinates.length ≤ D)
    (cache blueprint template : Bits)
    (hcache : cache=SubexpTaylorCacheControl.encodeCache SubexpTaylorRow.flat
      (SubexpTaylorCacheMap.caches p (D+1) M reduction theta (R+1) rows))
    (cacheLocal cleanupLocal : SubexpNodeCacheSetup.Data)
    (indexState bankState templateState : Data)
    (hactive : cacheLocal.stacks=activeStacks masters node ∘ Fin.castAdd 32)
    (hindex : indexState.stacks=indexed masters node cache index)
    (hraw : cleanupLocal.stacks=raw masters node cache index blueprint ∘ Fin.castAdd 32)
    (htemplate : templateState.stacks=templated masters index template)
    (h279 : bankState.stacks 279=masters 279) (h277 : bankState.stacks 277=masters 277)
    (h280 : bankState.stacks 280=masters 280) (h264 : bankState.stacks 264=masters 264)
    (hmodulus : masters 279=MatrixWordEncoding.modulus p)
    (hzero : masters 277=MatrixWordEncoding.zero p)
    (htokens : masters 280=ProgramEncoding.encodeRecords (MatrixImageEnumeration.tokens p))
    (hassignment : masters 258=SubexpFactorRoutingTraversal.words items++suffix)
    (hmetadata : masters 269=SupportSelectionProgram.metadataTable packing) :
    SubexpNodeCostAssembly.scale
      (NodePreludeSum.scale p D m D R (R+1) (baseWidth p (D+1)) (baseWidth p 1)
        modulus.length cacheLocal query nodes indexState bankState)
      PS
      (SubexpNodeTemplateSuffixBound.scale (p:=p) PS packing items suffix [] (R+1)
        (sourceContext masters D template) templateState cleanupLocal (templateContext masters D))
      ≤ 1000*OS^4 := by
  let S := OS
  have hS : 1 ≤ S := by dsimp [S,originalSize]; omega
  have hK : K ≤ S := by dsimp [S,originalSize]; omega
  have hvol : masterVolume masters ≤ S := by dsimp [S,originalSize]; omega
  have hmaster (i : Fin 288) (hi : i∈masterPorts) : (masters i).length ≤ S :=
    (master_le masters i hi).trans hvol
  have hdim : D ≤ S := by unfold NodeCacheBounds.scale at hK; omega
  have hR : R+1 ≤ S := by unfold NodeCacheBounds.scale at hK; omega
  have hB : baseWidth p (D+1) ≤ S := by unfold NodeCacheBounds.scale at hK; omega
  have hb : baseWidth p 1 ≤ S := by unfold NodeCacheBounds.scale at hK; omega
  have hr : r ≤ S := by dsimp [S,originalSize]; omega
  have hQ : Q ≤ S := by dsimp [S,originalSize]; omega
  have hI : SubexpSymbolicCost.indexBits D ≤ S := by dsimp [S,originalSize]; omega
  have hnode : node.length ≤ S := by dsimp [S,originalSize]; omega
  have hidx : index.length ≤ S := by dsimp [S,originalSize]; omega
  have hPS : PS ≤ S := by dsimp [S,originalSize,SubexpNodePacketInputBound.staticSize]; omega
  have hindexSize : SubexpNodePreludeBound.indexSize query nodes ≤ S := by
    dsimp [SubexpNodePreludeBound.indexSize,S,originalSize]
    omega
  have hcacheSize : SubexpNodePreludeBound.cacheInputSize cacheLocal ≤ 6*S := by
    rw [SubexpNodeCanonicalCostInputs.cacheInputSize_eq masters node cacheLocal hactive]
    have h := read_sum_le masters S hmaster [255,126,5,91,10] (by decide)
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at h
    omega
  have hbasisSize : SubexpNodeBasisExecution.inputVolume indexState+2 ≤ 13*S := by
    rw [basis_volume_eq masters node cache index indexState hindex]
    have h := read_sum_le masters S hmaster [269,266,261,264,270,271,272,276,282,283] (by decide)
    simp only [List.length_cons,List.length_nil] at h
    omega
  have hbankSize : SubexpNodePreludeBound.bankInputSize p D bankState ≤ 12*S := by
    rw [SubexpNodeCanonicalCostInputs.bankInputSize_eq p D masters bankState h279 h277 h280 h264]
    unfold SubexpNodeBankRuntimeBound.scale SubexpNodeBankMap.commonSize
    rw [←hmodulus,←hzero,←htokens,MatrixWordEncoding.width]
    have h := read_sum_le masters S hmaster [279,277,280,279,277,280,264] (by decide)
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at h
    omega
  have hprelude : NodePreludeSum.scale p D m D R (R+1) (baseWidth p (D+1))
      (baseWidth p 1) modulus.length cacheLocal query nodes indexState bankState ≤ 34*S := by
    unfold NodePreludeSum.scale
    omega
  have hcacheBytes : cache.length ≤ 53*S^4 := by
    rw [hcache]
    exact (NodeCacheBounds.cacheBytes_le p (D+1) M reduction theta m D R (R+1)
      (baseWidth p (D+1)) (baseWidth p 1) modulus.length rows hm hD le_rfl).trans
      (Nat.mul_le_mul_left 53 (Nat.pow_le_pow_left hK 4))
  have hcleanup : SubexpNodePreludeBound.cleanupInputSize cleanupLocal ≤ 11*S+cache.length := by
    rw [SubexpNodeCanonicalCostInputs.cleanupInputSize_eq masters node cache index blueprint cleanupLocal hraw]
    have h := read_sum_le masters S hmaster [255,126,5,91,10,10,10,10,10] (by decide)
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at h
    omega
  have hcontext : SubexpNodeTemplateReady.contextSize (templateContext masters D) ≤ 9*S := by
    have h := read_sum_le masters S hmaster [128,130,129,10,131,5,121] (by decide)
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at h
    unfold SubexpNodeTemplateReady.contextSize templateContext
    dsimp only
    omega
  have hsource : SubexpNodeCanonicalCostInputs.sourceScale p D masters index ≤ 40*S := by
    have h := read_sum_le masters S hmaster [129,10,122,123,129,10,5,124,122,123] (by decide)
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at h
    have hlog : Nat.log 2 p+1 ≤ S := by simpa only [baseWidth,one_mul] using hb
    unfold SubexpNodeCanonicalCostInputs.sourceScale SubexpSymbolicCost.parameterSize
      SubexpNodeJobsCostBound.scale
    omega
  have htemplateScale : SubexpTemplateCostBounds.scale p D (R+1) ≤ 10*S := by
    unfold SubexpTemplateCostBounds.scale
    omega
  have hwords : (SubexpFactorRoutingTraversal.words items++suffix).length ≤ S := by
    rw [←hassignment]
    exact hmaster 258 (by decide)
  have hmeta : (SupportSelectionProgram.metadataTable packing).length ≤ S := by
    rw [←hmetadata]
    exact hmaster 269 (by decide)
  have hsuffix : SubexpNodeTemplateSuffixBound.scale (p:=p) PS packing items suffix [] (R+1)
      (sourceContext masters D template) templateState cleanupLocal (templateContext masters D)
      ≤ 79*S+cache.length := by
    unfold SubexpNodeTemplateSuffixBound.scale SubexpNodeOriginalInputBound.originalScale
    rw [SubexpNodeCanonicalCostInputs.suffixSize_eq p D masters index template templateState htemplate]
    change PS+(SubexpFactorRoutingTraversal.words items++suffix).length+
      (SupportSelectionProgram.metadataTable packing).length+0+D+Q+r+baseWidth p 1+
      SubexpTemplateCostBounds.scale p D (R+1)+
      SubexpNodeCanonicalCostInputs.sourceScale p D masters index+1+
      SubexpNodePreludeBound.cleanupInputSize cleanupLocal+
      SubexpNodeTemplateReady.contextSize (templateContext masters D)+1 ≤ _
    omega
  have hS4 : S ≤ S^4 := Nat.le_self_pow (by decide) S
  change _ ≤ 1000*S^4
  unfold SubexpNodeCostAssembly.scale
  omega

end Bound
end SubexponentialSAT.Subexp.NodeCanonicalScale

#print axioms SubexponentialSAT.Subexp.NodeCanonicalScale.combinedScale_le

end OAI.Algorithms
