import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutSpec
import OAI.Algorithms.SubexponentialSAT.ComputablePackingSplit
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

namespace OAI.Algorithms

/-!
# Explicit enumeration by copying local block coordinates

The input is an explicit local decomposition.  Global coordinates are obtained
by copying this decomposition into each packed block and retaining the values
on leftover coordinates.  Finite tuples are encoded by ordinary mixed-radix
equivalences.  No basis of the global vector space is chosen or searched for.
-/

namespace SubexponentialSAT.Subexp.BlockwiseEnumeration

open scoped BigOperators

/-- Finite local coordinate data, supplied by the searches on one universal
block.  The inverses are data, not existentially chosen coordinate maps. -/
structure LocalData (K : Type*) [Semiring K] (U : Type*) [Fintype U]
    (r : ℕ) (W : Fin r → Submodule K (U → K)) where
  outerCount : ℕ
  innerCount : Fin r → ℕ
  outerBase : Fin outerCount → U → K
  incrementEquiv : ∀ g, Fin (innerCount g) ≃ W g
  assignmentEquiv : (U → K) ≃ (Fin outerCount × ∀ g, Fin (innerCount g))
  reconstruction : ∀ o x, assignmentEquiv.symm (o, x) =
    outerBase o + ∑ g, (incrementEquiv g (x g)).val

/-- Explicit base-`p` encoding of a vector over the prime residue ring. -/
def zmodVectorEquiv (p n : ℕ) [NeZero p] :
    (Fin n → ZMod p) ≃ Fin (p ^ n) :=
  (Equiv.piCongrRight fun _ => (ZMod.finEquiv p).symm.toEquiv).trans
    finFunctionFinEquiv

/-- Reindexing a function along supplied finite coordinate data. -/
def reindexFunction {A B K : Type*} (e : A ≃ B) : (B → K) ≃ (A → K) where
  toFun f a := f (e a)
  invFun f b := f (e.symm b)
  left_inv f := by funext b; simp
  right_inv f := by funext a; simp

section Packed

variable {K I U V : Type*} [Field K] [Fintype I] [Fintype U]
  [DecidableEq V] {r : ℕ} {W : Fin r → Submodule K (U → K)}

open ComputablePackingSplit

/-- The outer coordinates are the untouched values and one local outer index
for every block. -/
abbrev PackedOuter (e : I × U ↪ V) (D : LocalData K U r W) :=
  (Leftover e → K) × (I → Fin D.outerCount)

/-- One local inner index in every block. -/
abbrev PackedInner (D : LocalData K U r W) (g : Fin r) :=
  I → Fin (D.innerCount g)

/-- Restrict to each block, apply its supplied local coordinate map, and keep
the leftover values. The inverse uses only local reconstruction and scatter. -/
def packedAssignmentEquiv (e : I × U ↪ V) (D : LocalData K U r W) :
    (V → K) ≃ (PackedOuter e D × ∀ g, PackedInner (I := I) D g) where
  toFun v :=
    (((split e v).2, fun i => (D.assignmentEquiv ((split e v).1 i)).1),
      fun g i => (D.assignmentEquiv ((split e v).1 i)).2 g)
  invFun z := (split e).symm
    (fun i => D.assignmentEquiv.symm (z.1.2 i, fun g => z.2 g i), z.1.1)
  left_inv v := by
    apply (split e).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · funext i
      exact D.assignmentEquiv.symm_apply_apply _
    · rfl
  right_inv z := by
    dsimp only
    rw [LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        exact congrArg Prod.fst (D.assignmentEquiv.apply_symm_apply _)
    · funext g i
      exact congrFun (congrArg Prod.snd (D.assignmentEquiv.apply_symm_apply _)) g

/-- Scatter one local vector from the selected color into each block. -/
def packedIncrementEquiv (e : I × U ↪ V) (D : LocalData K U r W) (g : Fin r) :
    PackedInner (I := I) D g ≃ DirectSums.packedSubspace e (W g) where
  toFun x := ⟨assemble e (fun i => (D.incrementEquiv g (x i)).val, 0), by
    apply (DirectSums.mem_packedSubspace_iff e (W g) _).mpr
    constructor
    · intro i
      simpa only [assemble_on_block] using (D.incrementEquiv g (x i)).property
    · intro v hv
      exact assemble_outside e _ v hv⟩
  invFun v i := (D.incrementEquiv g).symm
    ⟨fun u => v.val (e (i, u)), DirectSums.packed_restriction_mem e (W g) v.property i⟩
  left_inv x := by
    funext i
    apply (D.incrementEquiv g).symm_apply_eq.mpr
    apply Subtype.ext
    funext u
    exact assemble_on_block e _ i u
  right_inv v := by
    apply Subtype.ext
    funext a
    change assemble e _ a = v.val a
    by_cases ha : a ∈ Set.range e
    · obtain ⟨⟨i, u⟩, rfl⟩ := ha
      rw [assemble_on_block]
      exact congrFun (congrArg Subtype.val
        ((D.incrementEquiv g).apply_symm_apply _)) u
    · rw [assemble_outside e _ a ha]
      exact (DirectSums.packed_zero_outside e (W g) v.property a ha).symm

/-- Copy the local complement values and the untouched coordinates. -/
def packedOuterBase (e : I × U ↪ V) (D : LocalData K U r W)
    (o : PackedOuter e D) : V → K :=
  assemble e (fun i => D.outerBase (o.2 i), o.1)

theorem packed_reconstruction (e : I × U ↪ V) (D : LocalData K U r W)
    (o : PackedOuter e D) (x : ∀ g, PackedInner (I := I) D g) :
    (packedAssignmentEquiv e D).symm (o, x) =
      packedOuterBase e D o + ∑ g, (packedIncrementEquiv e D g (x g)).val := by
  funext a
  by_cases ha : a ∈ Set.range e
  · obtain ⟨⟨i, u⟩, rfl⟩ := ha
    change assemble e _ (e (i, u)) = _
    simp only [assemble_on_block, packedOuterBase, packedIncrementEquiv,
      Equiv.coe_fn_mk, Pi.add_apply, Finset.sum_apply]
    simpa only [Pi.add_apply, Finset.sum_apply] using
      congrFun (D.reconstruction (o.2 i) (fun g => x g i)) u
  · change assemble e _ a = _
    simp only [assemble_outside e _ a ha, packedOuterBase, packedIncrementEquiv,
      Equiv.coe_fn_mk, Pi.add_apply, Finset.sum_apply, Pi.zero_apply,
      Finset.sum_const_zero, add_zero]

end Packed

section FiniteIndices

variable {p b l r : ℕ} [Fact p.Prime]
  {U V : Type*} [Fintype U] [Fintype V] [DecidableEq V]
  {W : Fin r → Submodule (ZMod p) (U → ZMod p)}

/-- A numerical index for the untouched values and copied local complements.
The supplied leftover enumeration is coordinate data, not a chosen basis. -/
def outerIndexEquiv (e : Fin b × U ↪ V) (D : LocalData (ZMod p) U r W)
    (leftoverEnum : Fin l ≃ ComputablePackingSplit.Leftover e) :
    PackedOuter e D ≃ Fin (p ^ l * D.outerCount ^ b) :=
  (Equiv.prodCongr
    ((reindexFunction leftoverEnum).trans (zmodVectorEquiv p l))
    finFunctionFinEquiv).trans finProdFinEquiv

/-- Encode the independent local inner indices in base `innerCount g`. -/
def innerIndexEquiv (D : LocalData (ZMod p) U r W) (g : Fin r) :
    PackedInner (I := Fin b) D g ≃ Fin (D.innerCount g ^ b) :=
  finFunctionFinEquiv

/-- The explicit global coordinate data. Only restriction, local coordinate
conversion, scattering, and mixed-radix arithmetic appear in the definitions. -/
def packedData (e : Fin b × U ↪ V) (D : LocalData (ZMod p) U r W)
    (leftoverEnum : Fin l ≃ ComputablePackingSplit.Leftover e)
    (G : Fin r → Submodule (ZMod p) (V → ZMod p))
    (hG : ∀ g, DirectSums.packedSubspace e (W g) = G g) :
    LocalData (ZMod p) V r G where
  outerCount := p ^ l * D.outerCount ^ b
  innerCount g := D.innerCount g ^ b
  outerBase o := packedOuterBase e D ((outerIndexEquiv e D leftoverEnum).symm o)
  incrementEquiv g := (innerIndexEquiv D g).symm.trans
    { toFun := fun x => ⟨(packedIncrementEquiv e D g x).val, by
        rw [← hG g]
        exact (packedIncrementEquiv e D g x).property⟩
      invFun := fun x => (packedIncrementEquiv e D g).symm ⟨x.val, by
        rw [hG g]
        exact x.property⟩
      left_inv := fun x => (packedIncrementEquiv e D g).symm_apply_apply x
      right_inv := by
        intro x
        apply Subtype.ext
        change ((packedIncrementEquiv e D g)
          ((packedIncrementEquiv e D g).symm ⟨x.val, _⟩)).val = x.val
        exact congrArg Subtype.val ((packedIncrementEquiv e D g).apply_symm_apply _) }
  assignmentEquiv := (packedAssignmentEquiv e D).trans
    (Equiv.prodCongr (outerIndexEquiv e D leftoverEnum)
      (Equiv.piCongrRight fun g => innerIndexEquiv D g))
  reconstruction o x := by
    exact packed_reconstruction e D ((outerIndexEquiv e D leftoverEnum).symm o)
      (fun g => (innerIndexEquiv D g).symm (x g))

@[simp] theorem packedData_outerCount (e : Fin b × U ↪ V)
    (D : LocalData (ZMod p) U r W)
    (leftoverEnum : Fin l ≃ ComputablePackingSplit.Leftover e)
    (G : Fin r → Submodule (ZMod p) (V → ZMod p))
    (hG : ∀ g, DirectSums.packedSubspace e (W g) = G g) :
    (packedData e D leftoverEnum G hG).outerCount = p ^ l * D.outerCount ^ b := rfl

@[simp] theorem packedData_innerCount (e : Fin b × U ↪ V)
    (D : LocalData (ZMod p) U r W)
    (leftoverEnum : Fin l ≃ ComputablePackingSplit.Leftover e)
    (G : Fin r → Submodule (ZMod p) (V → ZMod p))
    (hG : ∀ g, DirectSums.packedSubspace e (W g) = G g) (g : Fin r) :
    (packedData e D leftoverEnum G hG).innerCount g = D.innerCount g ^ b := rfl

end FiniteIndices

section Layout

variable {p k Δ r b l : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F E U : Type*} [Fintype V] [DecidableEq V] [Fintype F] [Fintype U]
  [Field E] [Algebra (ZMod p) E]
  {P : Factor.Pattern V F} {c : SubexpLayoutSpec.Parameters p k Δ r tau}

/-- Directly package explicit coordinate data into the enumeration interface
used by the counting algorithm. -/
def toEnumerationData (L : SubexpLayoutSpec.Layout (E := E) P c) (t : Fin c.Q)
    (D : LocalData (ZMod p) V r (L.K t)) : SubexpLayoutSpec.EnumerationData L t where
  outerCount := D.outerCount
  innerCount := D.innerCount
  outerBase := D.outerBase
  incrementEquiv := D.incrementEquiv
  assignmentEquiv := D.assignmentEquiv
  reconstruction := D.reconstruction

/-- The actual layout consumer. Equality with the packed local spaces is the
only bridge required; for the layout assembled from complete blocks it is
definitional equality. -/
def ofPackedSpaces (L : SubexpLayoutSpec.Layout (E := E) P c) (t : Fin c.Q)
    (e : Fin b × U ↪ V) {W : Fin r → Submodule (ZMod p) (U → ZMod p)}
    (D : LocalData (ZMod p) U r W)
    (leftoverEnum : Fin l ≃ ComputablePackingSplit.Leftover e)
    (hK : L.K t = fun g => DirectSums.packedSubspace e (W g)) :
    SubexpLayoutSpec.EnumerationData L t :=
  toEnumerationData L t
    (packedData e D leftoverEnum (L.K t) (fun g => congrFun hK.symm g))

/-- Use the executable bucket packing and its explicit leftover list directly. -/
def ofPackingData [DecidableEq U]
    (L : SubexpLayoutSpec.Layout (E := E) P c) (t : Fin c.Q)
    (packing : ConstructivePacking.PackingData V U)
    {W : Fin r → Submodule (ZMod p) (U → ZMod p)}
    (D : LocalData (ZMod p) U r W)
    (hK : L.K t = fun g =>
      DirectSums.packedSubspace packing.completeBlocks.embed (W g)) :
    SubexpLayoutSpec.EnumerationData L t :=
  ofPackedSpaces L t packing.completeBlocks.embed D packing.leftoverEquiv hK

end Layout

end SubexponentialSAT.Subexp.BlockwiseEnumeration

end OAI.Algorithms
