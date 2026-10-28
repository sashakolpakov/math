import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup

/-! The actual ring producer determines both the factor cutoff and the native
arithmetic cutoff. Its framed node stream uses the same increasing indices as
the physical cursor and the interpolation nodes. -/

noncomputable section

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafParametersProgram LeafProgram.PreparedSource

/-- The physical producer's node words are indexed in interpolation order. -/
def nodeBits (t d Q : ℕ) : List (List Bool) :=
  (LeafRingSetupProgram.nodeWords t d Q).map RingProgram.flat

@[simp] theorem nodeBits_length (t d Q : ℕ) : (nodeBits t d Q).length = Q := by
  simp [nodeBits]

theorem nodeBits_drop (t d Q : ℕ) (i : Fin Q) :
    (nodeBits t d Q).drop i.val =
      RingProgram.flat (RingNodeProgram.nodeCode t d (i.val+1)) ::
        (nodeBits t d Q).drop (i.val+1) := by
  rw [List.drop_eq_getElem_cons (by simp)]
  simp [nodeBits, LeafRingSetupProgram.nodeWords]

/-- This is an execution of the actual record reader on a suffix of the
generated table, with the precise node word used by the authentic factor. -/
theorem read_generated_node (regs : Fin 40 → Bool)
    (s : LeafNodeSamplesProgram.Store) (t d Q : ℕ) (i : Fin Q)
    (hs : s.source = Encoding.encodeList id ((nodeBits t d Q).drop i.val))
    (hp : s.payload = []) (hn : s.node = []) :
    Eval RingNodeSetup.readNode (9*(d*baseWidth 3 t)+8)
      (LeafNodeSamplesProgram.state regs s)
      (LeafNodeSamplesProgram.state (RingNodeSetup.nodeRegs regs)
        (RingNodeSetup.nodeRead s
          (RingProgram.flat (RingNodeProgram.nodeCode t d (i.val+1)))
          ((nodeBits t d Q).drop (i.val+1)))) := by
  have he := RingNodeSetup.readNode_eval regs s
    (RingProgram.flat (RingNodeProgram.nodeCode t d (i.val+1)))
    ((nodeBits t d Q).drop (i.val+1))
    (by simpa only [nodeBits_drop] using hs) hp hn
  simpa only [RingProgram.flat_length] using he

/-- The physical encoded cursor already pays for the decoded node and its
remaining suffix, so each reader restores the same boundary bound. -/
theorem read_generated_node_boundary (s : LeafNodeSamplesProgram.Store)
    (t d Q : ℕ) (i : Fin Q) (B : ℕ)
    (hs : s.source = Encoding.encodeList id ((nodeBits t d Q).drop i.val))
    (hentry : ∀ j, (LeafNodeSamplesProgram.tapes s j).length ≤ B) :
    ∀ j, (LeafNodeSamplesProgram.tapes
      (RingNodeSetup.nodeRead s
        (RingProgram.flat (RingNodeProgram.nodeCode t d (i.val+1)))
        ((nodeBits t d Q).drop (i.val+1))) j).length ≤ B := by
  have h := hentry 301
  change s.source.length ≤ B at h
  rw [hs, nodeBits_drop, Encoding.length_encodeList_cons] at h
  simp only [id_eq] at h
  apply RingNodeSetup.nodeRead_boundary _ _ _ B hentry
  · omega
  · omega

section Produced

variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)

include hp in
/-- Both physical serializations are supplied by the actual setup trace. -/
theorem produced_nodes :
    e.stacks 300 = Encoding.encodeList id (nodeBits (m.val 33) (m.val 34) (m.val 21)) ∧
    e.stacks 256 = (nodeBits (m.val 33) (m.val 34) (m.val 21)).flatten :=
  ⟨hp.framedNodes, hp.flatNodes⟩

include hp in
/-- The actual producer supplies the arithmetic words, with the original
searched ring and its scalar cache. No legacy node-evaluator record is needed. -/
theorem produced_arithmetic_words :
    e.stacks 194 = M.bits ∧
    e.stacks 201 = RingTriple.tableEncoding (HornerProgram.modelTable (m.val 33)
      (IrreducibleSearch.data hd) M cache) ∧
    (e.stacks 202).length = baseWidth 3 (m.val 33) ∧
    e.stacks 203 = cache.zero.val ∧ (e.stacks 204).length = m.val 34 ∧
    e.stacks 212 = List.replicate (m.val 33) true ∧
    e.stacks 243 = List.replicate (m.val 42) true ∧
    e.stacks 207 = RingProgram.flat (RingProgram.modelProgram (m.val 33)
      (IrreducibleSearch.data hd) M cache).oneRun.1 ∧
    e.stacks 280 = RingProgram.flat (RingProgram.modelProgram (m.val 33)
      (IrreducibleSearch.data hd) M cache).zeroRun.1 ∧
    e.stacks 211 = RingProgram.flat (LeafProgram.Constants.constantCode
      (m.val 34) cache.minusOne cache.zero) := by
  refine ⟨hp.caches.modulus, hp.native.table, hp.caches.width, hp.caches.scalarZero,
    hp.caches.degree, hp.caches.precision, hp.jetOrder, hp.caches.fullOne_model,
    hp.caches.fullZero_model, ?_⟩
  exact hp.caches.fullMinusOne.trans
    (LeafProgram.Constants.constantCode_flat _ _ _).symm

/-- The stored negative unit has its actual meaning in the produced ring. -/
theorem produced_minusOne_decode :
    (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
      (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero) = -1 :=
  LeafProgram.Constants.minusOne_decode _ ht hd _ M cache

variable (s : LeafHeadSetupProgram.Native.Inputs) (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height
      (LeafHeadSetupProgram.unary s.R) s.width words)
    (hfield : s.Q < 3^(m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (hJ : 0 < m.val 42) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)

/-- Moving the physical node cursor changes theta, not the produced ring or
its source parameters. The only node-dependent parameter field is a proof. -/
theorem produced_parameters_node_irrel (i j : Fin s.Q) :
    LayoutProgram.SourceBank.Parameters.ofProduced {s with node := i} words hc
      m ht hd M cache half e hp hfield =
    LayoutProgram.SourceBank.Parameters.ofProduced {s with node := j} words hc
      m ht hd M cache half e hp hfield := rfl

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp
  hfield q hv (m.val 42) hJ source hsource

/-- The constructor ties the semantic cutoff, machine cutoff, and physical
jet-order word together before any per-node query is evaluated. -/
theorem produced_factor_parameters :
    (spec).u = (spec).p.t ∧ (spec).p.t = m.val 33 ∧
    (spec).J = m.val 42 ∧
    (spec).theta = RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1) ∧
    e.stacks 212 = List.replicate (spec).u true ∧
    e.stacks 243 = List.replicate (spec).J true := by
  exact ⟨rfl, rfl, rfl, rfl, hp.caches.precision, hp.jetOrder⟩

/-- The actual factor uses precisely the plans, packing, source and bit width
of its authentic input constructor; the finite reindexing changes no plan. -/
theorem produced_factor_source :
    (spec).ps = s.plans ∧
    (spec).packing = PackingIncidenceInput.reindexPacking s.plans_length.symm s.packing ∧
    (spec).source = source ∧ (spec).bitWidth = q.width.length :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Source-layout parameters are the concrete native input and bootstrap
cache fields used by the integer row loader. -/
theorem produced_factor_layout :
    (spec).p.R = s.R ∧ (spec).p.width = s.width ∧
    (spec).p.aWord = s.height ∧ (spec).p.hwords = words ∧
    (spec).p.power = s.power :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The same stored theta decodes to the node used by interpolation. -/
theorem produced_factor_theta :
    (spec).p.ops.decode (spec).theta =
      (IrreducibleSearch.data hd).node (m.val 33) s.Q ht hfield s.node :=
  nativeSpecOfInputs_theta s m ht hd words hc M cache half e hp
    hfield q hv (m.val 42) hJ source hsource

end Produced

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeMetadata
