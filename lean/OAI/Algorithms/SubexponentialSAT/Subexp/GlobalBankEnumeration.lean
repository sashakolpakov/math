import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixCoefficientOrder
import OAI.Algorithms.SubexponentialSAT.Subexp.ComputedBlockwiseEnumeration

namespace OAI.Algorithms

/-!
# Layout vectors in the physical matrix-image output order

This adapter uses the actual reversed tuple order of the matrix-image
program. Its outer and inner lists are exactly the emitted bank lists for
the explicit global matrices, while its reconstruction proof comes from
the checked local pairs and actual packing.
-/

namespace SubexponentialSAT.Subexp.GlobalBankEnumeration

open scoped BigOperators
open BlockSearch LocalEnumeration GlobalBasis GlobalKernel
open ComputablePackingSplit MatrixWordEncoding BlockCoefficientProgram

variable {p D r b l : ℕ} [Fact p.Prime]
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {n m : Fin r → ℕ}
variable (color : U → Fin r) (sideIndex : ∀ g, Fin (n g) ≃ ColorFiber color g)
variable (constraint : ∀ g, Fin (m g) → Fin (n g) → ZMod p)
variable (pairs : ∀ g, Candidate (ZMod p) (n g) × Candidate (ZMod p) (n g))
variable (good : ∀ g, GoodPair (constraint g) (pairs g))
variable (alphabet : List (ZMod p)) (complete : ∀ x, x ∈ alphabet)
variable (packing : Fin b × U ↪ Fin D) (leftovers : Fin l ≃ Leftover packing)
variable (G : Fin r → Submodule (ZMod p) (Fin D → ZMod p))
variable (hG : ∀ g, DirectSums.packedSubspace packing (sideKernel color sideIndex constraint g) = G g)

def data : BlockwiseEnumeration.LocalData (ZMod p) (Fin D) r G :=
  GlobalEnumeration.data color sideIndex constraint pairs good alphabet complete packing leftovers G hG
    (MatrixCoefficientOrder.order p (outerEnumeration (b := b) (l := l) pairs).equivFin)
    (fun g => MatrixCoefficientOrder.order p (innerEnumeration (b := b) pairs g).equivFin)

theorem outerBase_eq (o : Fin (data color sideIndex constraint pairs good alphabet complete packing leftovers G hG).outerCount) :
    (data color sideIndex constraint pairs good alphabet complete packing leftovers G hG).outerBase o =
      matrixMap (outerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers)
        (MatrixCoefficientOrder.coefficientsEquiv p (outerList (b := b) (l := l) pairs).length o) := by
  funext v
  exact GlobalEnumeration.outerMap_reindexed_apply color sideIndex constraint pairs good alphabet complete
    packing leftovers _ v

theorem increment_eq (g : Fin r)
    (i : Fin ((data color sideIndex constraint pairs good alphabet complete packing leftovers G hG).innerCount g)) :
    ((data color sideIndex constraint pairs good alphabet complete packing leftovers G hG).incrementEquiv g i).val =
      matrixMap (innerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers g)
        (MatrixCoefficientOrder.coefficientsEquiv p (innerList (b := b) pairs g).length i) := by
  funext v
  change GlobalEnumeration.innerMap color sideIndex constraint pairs good alphabet complete packing leftovers g
    (fun c => MatrixCoefficientOrder.coefficientsEquiv p (innerList (b := b) pairs g).length i
      ((innerEnumeration (b := b) pairs g).equivFin.symm c)) v = _
  rw [GlobalEnumeration.innerMap_eq]
  exact indexedKernelLinear_apply color sideIndex constraint pairs good packing alphabet complete leftovers g _ v

/-- Encoding the actual outer array gives exactly the bank list emitted by
the physical matrix-image program for the constructed outer matrix. -/
theorem outerBankRecords_eq :
    (List.ofFn (data color sideIndex constraint pairs good alphabet complete packing leftovers G hG).outerBase).map
      (fun v => (vectorWords p v).flatten) =
    MatrixImageEnumeration.bankRecords p
      (outerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers) := by
  rw [List.map_ofFn]
  calc
    _ = List.ofFn (fun o => MatrixImageEnumeration.bank p
        (outerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers)
        (MatrixCoefficientOrder.coefficientsEquiv p (outerList (b := b) (l := l) pairs).length o)) := by
      congr 1
      funext o
      rw [Function.comp_apply, outerBase_eq]
      rfl
    _ = _ := MatrixCoefficientOrder.bankRecords_eq p _

/-- The color-specific increment array has the same actual output order and
the same scalar payloads as its physical matrix-image call. -/
theorem innerBankRecords_eq (g : Fin r) :
    (List.ofFn (fun i => ((data color sideIndex constraint pairs good alphabet complete packing leftovers G hG).incrementEquiv g i).val)).map
      (fun v => (vectorWords p v).flatten) =
    MatrixImageEnumeration.bankRecords p
      (innerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers g) := by
  rw [List.map_ofFn]
  calc
    _ = List.ofFn (fun i => MatrixImageEnumeration.bank p
        (innerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers g)
        (MatrixCoefficientOrder.coefficientsEquiv p (innerList (b := b) pairs g).length i)) := by
      congr 1
      funext i
      rw [Function.comp_apply, increment_eq]
      rfl
    _ = _ := MatrixCoefficientOrder.bankRecords_eq p _

/-- The executed record uses directly defined packed carriers. Its
interpretation as the semantic layout space is a later proof-only cast;
no abstract layout value is evaluated to choose or enumerate vectors. -/
def computedData : BlockwiseEnumeration.LocalData (ZMod p) (Fin D) r
    (fun g => ComputedBlockwiseEnumeration.packedSpace packing
      (sideKernel color sideIndex constraint g)) :=
  data color sideIndex constraint pairs good alphabet complete packing leftovers
    (fun g => ComputedBlockwiseEnumeration.packedSpace packing
      (sideKernel color sideIndex constraint g))
    (fun g => (ComputedBlockwiseEnumeration.packedSpace_eq packing
      (sideKernel color sideIndex constraint g)).symm)

theorem computedData_outerBankRecords_eq :
    (List.ofFn (computedData color sideIndex constraint pairs good alphabet complete packing leftovers).outerBase).map
      (fun v => (vectorWords p v).flatten) =
    MatrixImageEnumeration.bankRecords p
      (outerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers) :=
  outerBankRecords_eq color sideIndex constraint pairs good alphabet complete packing leftovers _ _

theorem computedData_innerBankRecords_eq (g : Fin r) :
    (List.ofFn (fun i => ((computedData color sideIndex constraint pairs good alphabet complete packing leftovers).incrementEquiv g i).val)).map
      (fun v => (vectorWords p v).flatten) =
    MatrixImageEnumeration.bankRecords p
      (innerMatrix color sideIndex constraint pairs good alphabet complete packing leftovers g) :=
  innerBankRecords_eq color sideIndex constraint pairs good alphabet complete packing leftovers _ _ g

end SubexponentialSAT.Subexp.GlobalBankEnumeration

end OAI.Algorithms
