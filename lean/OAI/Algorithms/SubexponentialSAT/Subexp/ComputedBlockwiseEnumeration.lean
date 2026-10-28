import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockwiseEnumeration

namespace OAI.Algorithms

/-!
# Computable carriers for packed enumeration data

The carrier is stated directly by block restrictions and zeros outside the
packing.  Equality with the original semantic range construction occurs only
in proofs.  A whole-record cast then exposes the original mathematical type
without executing its noncomputable submodule constructor.
-/

namespace SubexponentialSAT.Subexp.ComputedBlockwiseEnumeration

open BlockwiseEnumeration

variable {K I U V : Type*} [Field K]

/-- Explicit membership presentation of the packed direct sum. -/
def packedSpace (e : I × U ↪ V) (W : Submodule K (U → K)) :
    Submodule K (V → K) where
  carrier := fun f => (∀ i, (fun u => f (e (i, u))) ∈ W) ∧
    ∀ v, v ∉ Set.range e → f v = 0
  zero_mem' := by
    constructor
    · intro i
      exact W.zero_mem
    · intro v hv
      rfl
  add_mem' := by
    intro f g hf hg
    constructor
    · intro i
      exact W.add_mem (hf.1 i) (hg.1 i)
    · intro v hv
      change f v + g v = 0
      rw [hf.2 v hv, hg.2 v hv, zero_add]
  smul_mem' := by
    intro c f hf
    constructor
    · intro i
      exact W.smul_mem c (hf.1 i)
    · intro v hv
      change c • f v = 0
      rw [hf.2 v hv, smul_zero]

theorem packedSpace_eq (e : I × U ↪ V) (W : Submodule K (U → K)) :
    packedSpace e W = DirectSums.packedSubspace e W := by
  ext f
  exact (DirectSums.mem_packedSubspace_iff e W f).symm

section Data

variable {p b l r : ℕ} [Fact p.Prime] [Fintype U] [Fintype V] [DecidableEq V]
  {W : Fin r → Submodule (ZMod p) (U → ZMod p)}

/-- Global data constructed entirely using the explicit carrier. -/
def computedData (e : Fin b × U ↪ V) (D : LocalData (ZMod p) U r W)
    (leftoverEnum : Fin l ≃ ComputablePackingSplit.Leftover e) :
    LocalData (ZMod p) V r (fun g => packedSpace e (W g)) :=
  packedData e D leftoverEnum (fun g => packedSpace e (W g))
    (fun g => (packedSpace_eq e (W g)).symm)

/-- The same executable record at the original semantic family of subspaces.
The equality transport is erased; no semantic range constructor is executed. -/
def semanticData (e : Fin b × U ↪ V) (D : LocalData (ZMod p) U r W)
    (leftoverEnum : Fin l ≃ ComputablePackingSplit.Leftover e) :
    LocalData (ZMod p) V r (fun g => DirectSums.packedSubspace e (W g)) :=
  cast (congrArg (fun G => LocalData (ZMod p) V r G)
    (funext (fun g => packedSpace_eq e (W g)))) (computedData e D leftoverEnum)

end Data

end SubexponentialSAT.Subexp.ComputedBlockwiseEnumeration

end OAI.Algorithms
