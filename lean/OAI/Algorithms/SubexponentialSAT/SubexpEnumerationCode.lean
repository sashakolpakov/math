import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpComputedWeights
import OAI.Algorithms.SubexponentialSAT.SubexpProgramBuilder

namespace OAI.Algorithms

/-!
# Finite-list adapter for supplied multicolor enumeration data

The input is `EnumerationData`, whose vector arrays and bijections must be
constructed separately. This module creates actual lists using `List.ofFn`
and `List.finRange`, proves their coverage and lengths, and supplies the
coordinate-support lists used by the executable separated evaluator.
No basis, complement, or enumeration is selected by classical choice here.
-/

namespace SubexponentialSAT.SubexpEnumerationCode

open scoped BigOperators
open SubexpLayoutSpec

variable {D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F E : Type*} [Fintype F] [Field E] [Algebra (ZMod p) E]
  {P : Factor.Pattern (Fin D) F} {c : Parameters p k Δ r tau}
  {L : Layout (E := E) P c} {t : Fin c.Q}

/-- Explicit outer basepoint list, in the supplied array order. -/
def outerBases (data : EnumerationData L t) : List (Fin D → ZMod p) :=
  List.ofFn data.outerBase

/-- Each color's explicit increment list. No product of these lists is formed. -/
def innerIncrements (data : EnumerationData L t) (g : Fin r) :
    List (Fin D → ZMod p) := List.ofFn (data.increment g)

/-- Support coordinates in increasing ambient-index order. -/
def supportLists (L : Layout (E := E) P c) (t : Fin c.Q) (g : Fin r) : List (Fin D) :=
  (List.finRange D).filter (fun i => decide (i ∈ L.support t g))

/-- Complement coordinates, obtained by a finite filter over the ambient indices. -/
def outsideList (L : Layout (E := E) P c) (t : Fin c.Q) : List (Fin D) :=
  SubexpComputedWeights.outsideCoordinates (supportLists L t)

@[simp] theorem outerBases_length (data : EnumerationData L t) :
    (outerBases data).length = data.outerCount := List.length_ofFn

@[simp] theorem innerIncrements_length (data : EnumerationData L t) (g : Fin r) :
    (innerIncrements data g).length = data.innerCount g := List.length_ofFn

theorem outerBase_injective (data : EnumerationData L t) :
    Function.Injective data.outerBase := by
  intro a b hab
  have hz (o : Fin data.outerCount) :
      data.assignmentEquiv.symm (o, fun g => data.zeroIndex g) = data.outerBase o := by
    rw [data.reconstruct_eq]
    simp
  have heq := data.assignmentEquiv.symm.injective
    ((hz a).trans (hab.trans (hz b).symm))
  exact congrArg Prod.fst heq

theorem increment_injective (data : EnumerationData L t) (g : Fin r) :
    Function.Injective (data.increment g) := by
  intro i j hij
  exact (data.incrementEquiv g).injective (Subtype.ext hij)

theorem outerBases_nodup (data : EnumerationData L t) : (outerBases data).Nodup :=
  List.nodup_ofFn_ofInjective (outerBase_injective data)

theorem innerIncrements_nodup (data : EnumerationData L t) (g : Fin r) :
    (innerIncrements data g).Nodup :=
  List.nodup_ofFn_ofInjective (increment_injective data g)

@[simp] theorem mem_outerBases (data : EnumerationData L t) (x : Fin D → ZMod p) :
    x ∈ outerBases data ↔ ∃ o, data.outerBase o = x := List.mem_ofFn

@[simp] theorem mem_innerIncrements (data : EnumerationData L t) (g : Fin r)
    (x : Fin D → ZMod p) : x ∈ innerIncrements data g ↔ x ∈ L.K t g := by
  rw [innerIncrements, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact data.increment_mem g i
  · intro hx
    obtain ⟨i, hi⟩ := (data.incrementEquiv g).surjective ⟨x, hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩

/-- Coverage by the supplied basepoints and individual increment lists,
without constructing their Cartesian product as a list. -/
theorem assignments_covered (data : EnumerationData L t) (x : Fin D → ZMod p) :
    ∃ b ∈ outerBases data, ∃ inc : Fin r → (Fin D → ZMod p),
      (∀ g, inc g ∈ innerIncrements data g) ∧ x = b + ∑ g, inc g := by
  let z := data.assignmentEquiv x
  refine ⟨data.outerBase z.1, ?_, (fun g => data.increment g (z.2 g)), ?_, ?_⟩
  · exact (mem_outerBases data _).mpr ⟨z.1, rfl⟩
  · intro g
    exact (mem_innerIncrements data g _).mpr (data.increment_mem g (z.2 g))
  · exact (data.assignmentEquiv.symm_apply_apply x).symm.trans
      (data.reconstruct_eq z.1 z.2)

theorem supportLists_nodup (L : Layout (E := E) P c) (t : Fin c.Q) (g : Fin r) :
    (supportLists L t g).Nodup := (List.nodup_finRange D).filter _

@[simp] theorem supportLists_toFinset (L : Layout (E := E) P c) (t : Fin c.Q)
    (g : Fin r) : (supportLists L t g).toFinset = L.support t g := by
  ext i
  simp [supportLists]

theorem supportLists_length (L : Layout (E := E) P c) (t : Fin c.Q) (g : Fin r) :
    (supportLists L t g).length = (L.support t g).card := by
  rw [← List.toFinset_card_of_nodup (supportLists_nodup L t g), supportLists_toFinset]

theorem outsideList_nodup (L : Layout (E := E) P c) (t : Fin c.Q) :
    (outsideList L t).Nodup := SubexpComputedWeights.outsideCoordinates_nodup _

@[simp] theorem outsideList_toFinset (L : Layout (E := E) P c) (t : Fin c.Q) :
    (outsideList L t).toFinset = (Finset.univ.biUnion (L.support t))ᶜ := by
  simp only [outsideList, SubexpComputedWeights.outsideCoordinates_toFinset,
    supportLists_toFinset]

theorem outerBases_length_exact (data : EnumerationData L t) :
    (outerBases data).length = p ^ (D - ∑ g, Module.finrank (ZMod p) (L.K t g)) := by
  simpa only [outerBases_length, Fintype.card_fin] using data.outerCount_eq

theorem innerIncrements_length_exact (data : EnumerationData L t) (g : Fin r) :
    (innerIncrements data g).length = p ^ Module.finrank (ZMod p) (L.K t g) := by
  rw [innerIncrements_length, data.innerCount_eq]

theorem sum_inner_lengths (data : EnumerationData L t) :
    (∑ g, (innerIncrements data g).length) =
      ∑ g, p ^ Module.finrank (ZMod p) (L.K t g) := by
  simp only [innerIncrements_length_exact]

theorem list_work_eq (data : EnumerationData L t) :
    (outerBases data).length * (∑ g, (innerIncrements data g).length) =
      data.iterationCount := by
  simp only [outerBases_length, innerIncrements_length, EnumerationData.iterationCount]

theorem list_work_bound (data : EnumerationData L t) :
    (((outerBases data).length * (∑ g, (innerIncrements data g).length) : ℕ) : ℝ) ≤
      (r : ℝ) * (p : ℝ) ^ (SubexpCosetCount.alpha r (tau : ℝ) * D) := by
  rw [list_work_eq]
  simpa only [Fintype.card_fin] using data.iterationCount_bound

/-- The executable dot product at the one-color input is exactly the beta of
the full reconstructed assignment. Coordinate and residue lifts stay distinct. -/
theorem compiled_beta_eq {Λ : Type*} [CommRing Λ]
    (data : EnumerationData L t) (lifted : LiftedLayout L Λ)
    (coordinateLift : ZMod p → Λ)
    (hLift : ∀ a, lifted.residue (coordinateLift a) = algebraMap (ZMod p) E a)
    (s : CosetInvariance.ResidueSection lifted.residue)
    (e : F) (v : {v // v ∈ P.scope e})
    (o : Fin data.outerCount) (x : ∀ g, Fin (data.innerCount g)) :
    SubexpInputCode.beta s.lift (fun w => (L.row e v w).eval (L.node t))
      (fun w => algebraMap (ZMod p) E
        (data.outerBase o w + data.increment (L.color e t) (x (L.color e t)) w)) =
      (lifted.liftedRow coordinateLift hLift t e v).beta s
        (data.assignmentEquiv.symm (o, x)) := by
  rw [lifted.beta_enumeration_eq coordinateLift hLift s t data e v o x,
    CosetInvariance.LiftedRow.beta_eq_lift_row, SubexpInputCode.beta_eq_lift_sum]
  rfl

section Programs

variable {K A : Type*} [Semiring K] [CommRing A] {q : ℕ}

/-- Build each group expression at the basepoint plus its own color increment.
The residue-field lift and coordinate-weight lift are deliberately separate. -/
def groupCode (data : EnumerationData L t) (embed : ZMod p → K)
    (betaLift : K → A) (cache : List (List A))
    (factors : List (SubexpProgramBuilder.FactorData D p q r K A))
    (_a : Fin D → ℕ) (o : Fin data.outerCount) (g : Fin r)
    (j : Fin (data.innerCount g)) : Algorithm.Expr (SymbolicCost.CoeffList D A) :=
  SubexpProgramBuilder.groupExpr betaLift cache factors g
    (fun i => embed (data.outerBase o i + data.increment g j i))

/-- The actual list program, built directly from the supplied vector arrays. -/
def programBlocks (data : EnumerationData L t) (embed : ZMod p → K)
    (betaLift : K → A) (weightLift : ZMod p → A) (cache : List (List A))
    (factors : List (SubexpProgramBuilder.FactorData D p q r K A)) (a : Fin D → ℕ) :
    List (SubexpAlgorithm.Block (SymbolicCost.CoeffList D A)) :=
  SubexpProgramBuilder.blocks embed betaLift weightLift cache factors
    (supportLists L t) (outsideList L t) (outerBases data) (innerIncrements data) a

/-- Mapping the finite vector arrays produces exactly the index-based program
whose weight and finite-sum correctness were already proved. -/
theorem programBlocks_eq_computedBlocks (data : EnumerationData L t)
    (embed : ZMod p → K) (betaLift : K → A) (weightLift : ZMod p → A)
    (cache : List (List A))
    (factors : List (SubexpProgramBuilder.FactorData D p q r K A)) (a : Fin D → ℕ) :
    programBlocks data embed betaLift weightLift cache factors a =
      SubexpComputedWeights.computedBlocks data (supportLists L t) weightLift
        (groupCode data embed betaLift cache factors) a := by
  simp only [programBlocks, SubexpProgramBuilder.blocks, outerBases, innerIncrements,
    SubexpComputedWeights.computedBlocks, SubexpKernelCorrectness.buildBlocks,
    SubexpProgramBuilder.block, SubexpAlgorithm.Block.ofFibers,
    SubexpComputedWeights.outsideCode, SubexpComputedWeights.insideCode,
    groupCode, outsideList, SubexpProgramBuilder.shifted, List.ofFn_eq_map,
    List.map_map, Function.comp_def]

def executeProgram (data : EnumerationData L t) (embed : ZMod p → K)
    (betaLift : K → A) (weightLift : ZMod p → A) (cache : List (List A))
    (factors : List (SubexpProgramBuilder.FactorData D p q r K A)) : List A :=
  SubexpAlgorithm.executeJet (programBlocks data embed betaLift weightLift cache factors)

/-- Every actual list block has the expected number of independently scanned
inner terms, and the total equals the derived enumeration count. -/
theorem programBlocks_innerCalls (data : EnumerationData L t)
    (embed : ZMod p → K) (betaLift : K → A) (weightLift : ZMod p → A)
    (cache : List (List A))
    (factors : List (SubexpProgramBuilder.FactorData D p q r K A)) (a : Fin D → ℕ) :
    ((programBlocks data embed betaLift weightLift cache factors a).map
      SubexpAlgorithm.Block.innerCalls).sum = data.iterationCount := by
  simp only [programBlocks, SubexpProgramBuilder.blocks, List.map_map, Function.comp_def,
    SubexpProgramBuilder.block_innerCalls, List.map_const', List.sum_replicate,
    smul_eq_mul, outerBases_length, innerIncrements_length, EnumerationData.iterationCount]

/-- The builder's expression-size estimate specialized to the exact supplied
array lengths. This bounds expression nodes, not Turing-machine steps. -/
theorem programBlocks_size_le (data : EnumerationData L t)
    (embed : ZMod p → K) (betaLift : K → A) (weightLift : ZMod p → A)
    (cache : List (List A))
    (factors : List (SubexpProgramBuilder.FactorData D p q r K A))
    (a : Fin D → ℕ) (M ell : ℕ)
    (hc : ∀ i : Fin p, (cache.getD i.val []).length ≤ ell)
    (hk : ∀ f ∈ factors, f.arity ≤ k) (hM : ∀ f ∈ factors, f.table.length ≤ M) :
    (SubexpAlgorithm.rawMomentExpression
      (programBlocks data embed betaLift weightLift cache factors a)).size ≤
        ((SubexpProgramBuilder.groupBudget factors.length k M ell + 3) *
          (∑ g, data.innerCount g) + 2 * r + 4) * data.outerCount + 1 := by
  simpa only [programBlocks, outerBases_length, innerIncrements_length] using
    SubexpProgramBuilder.blocks_size_le embed betaLift weightLift cache factors
      (supportLists L t) (outsideList L t) (outerBases data) (innerIncrements data)
      a k M ell hc hk hM

/-- The remaining program premises are local group-expression semantics and
their independently provable own-color invariance. All list enumeration and
computed-weight premises are discharged by this adapter. -/
theorem executeProgram_eq_separatedJet (data : EnumerationData L t)
    (embed : ZMod p → K) (betaLift : K → A) (weightLift : ZMod p → A)
    (cache : List (List A))
    (factors : List (SubexpProgramBuilder.FactorData D p q r K A))
    (groups : Fin r → (Fin D → ZMod p) → SymbolicCost.Poly D A)
    (hgroup : ∀ o g j,
      ((SubexpProgramBuilder.groupExpr betaLift cache factors g
        (fun i => embed (data.outerBase o i + data.increment g j i))).map
          SymbolicCost.denote).eval = groups g (data.outerBase o + data.increment g j))
    (hinvariant : ∀ o g x y, x g = y g →
      groups g ((SubexpComputedWeights.enumerationFiberEquiv data).symm ⟨o, x⟩) =
        groups g ((SubexpComputedWeights.enumerationFiberEquiv data).symm ⟨o, y⟩)) :
    executeProgram data embed betaLift weightLift cache factors =
      (List.range D).map fun j =>
        (SubexpCounting.separatedJet (D + 1) D
          (SubexpComputedWeights.enumerationFiberEquiv data)
          (fun _ g => data.zeroIndex g) groups
          (fun a o => SubexpComputedWeights.outsideValue (supportLists L t)
            weightLift (data.outerBase o) a)
          (fun a o g y => SubexpComputedWeights.insideValue (supportLists L t)
            weightLift (data.outerBase o) (data.increment g y) a g)).coeff j := by
  have hblocks : programBlocks data embed betaLift weightLift cache factors =
      SubexpComputedWeights.computedBlocks data (supportLists L t) weightLift
        (groupCode data embed betaLift cache factors) := by
    funext a
    exact programBlocks_eq_computedBlocks data embed betaLift weightLift cache factors a
  unfold executeProgram
  rw [hblocks]
  apply SubexpComputedWeights.execute_computedBlocks_eq_separatedJet data (supportLists L t)
    (supportLists_nodup L t) (supportLists_toFinset L t) weightLift
    (groupCode data embed betaLift cache factors) groups
  · intro a o g j
    exact hgroup o g j
  · exact hinvariant

end Programs

end SubexponentialSAT.SubexpEnumerationCode

end OAI.Algorithms
