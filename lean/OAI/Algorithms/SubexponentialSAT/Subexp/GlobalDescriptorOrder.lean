import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisDescriptors
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisPrepareColumns

namespace OAI.Algorithms

/-!
# The descriptor generator uses the global matrix's column order

These are equalities of lists, including every leftover, block, color, and
local column position. No permutation of the emitted matrices is needed.
-/

namespace SubexponentialSAT.Subexp.GlobalDescriptorOrder

open GlobalBasis GlobalBasisDescriptors GlobalBasisProgram BlockSearch
open GlobalBasisColumns (Descriptor)

theorem map_finRange_val {A : Type*} (N : ℕ) (f : ℕ → A) :
    (List.finRange N).map (fun i => f i.val) = (List.range N).map f := by
  change (List.finRange N).map (f ∘ (fun i : Fin N => i.val)) = _
  rw [← List.map_map, List.map_coe_finRange]

theorem flatMap_finRange_val {A : Type*} (N : ℕ) (f : ℕ → List A) :
    (List.finRange N).flatMap (fun i => f i.val) = (List.range N).flatMap f := by
  rw [← List.flatMap_map, List.map_coe_finRange]

theorem zipIdx_ofFn {A : Type*} {r : ℕ} (f : Fin r → A) :
    (List.ofFn f).zipIdx = (List.finRange r).map (fun g => (f g, g.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

variable {p r b l : ℕ} {n : Fin r → ℕ}
variable (pairs : ∀ g, Candidate (ZMod p) (n g) × Candidate (ZMod p) (n g))

theorem innerDescriptors_eq (g : Fin r) :
    (innerList (b := b) pairs g).map (innerDescriptor pairs g) =
      innerDescriptors b g.val (pairs g).1.1.val := by
  simp only [innerList, List.product, List.map_flatMap, List.map_map,
    Function.comp_def, innerDescriptor, innerDescriptors]
  simp only [map_finRange_val]
  exact flatMap_finRange_val b
    (fun block => (List.range (pairs g).1.1.val).map (Descriptor.localColumn block g.val))

/-- Only dimensions and split positions affect the generated descriptor
order; the local matrix payloads are carried unchanged by the assembler. -/
theorem outerDescriptors_eq (qs : Fin r → GlobalBasisComplementColumns.LocalData)
    (hrank : ∀ g, (qs g).rank = (pairs g).1.1.val)
    (hN : ∀ g, (qs g).N = (pairs g).1.1.val + (pairs g).2.1.val) :
    (outerList (b := b) (l := l) pairs).map (outerDescriptor pairs) =
      outerDescriptors b l (List.ofFn qs) := by
  simp only [outerDescriptors, zipIdx_ofFn, List.flatMap_map,
    hrank, hN, Nat.add_sub_cancel_left]
  simp only [outerList, localOuterList, List.product, List.sigma, List.map_append,
    List.map_flatMap, List.map_map, Function.comp_def, outerDescriptor]
  rw [map_finRange_val l Descriptor.leftover]
  apply congrArg (List.append ((List.range l).map Descriptor.leftover))
  calc
    _ = (List.finRange b).flatMap (fun block =>
        (List.finRange r).flatMap fun g =>
          (List.range (pairs g).2.1.val).map fun j =>
            Descriptor.localColumn block.val g.val ((pairs g).1.1.val + j)) := by
      apply List.flatMap_congr
      intro block _
      apply List.flatMap_congr
      intro g _
      exact map_finRange_val (pairs g).2.1.val
        (fun j => Descriptor.localColumn block.val g.val ((pairs g).1.1.val + j))
    _ = _ := flatMap_finRange_val b (fun block =>
      (List.finRange r).flatMap fun g =>
        (List.range (pairs g).2.1.val).map fun j =>
          Descriptor.localColumn block g.val ((pairs g).1.1.val + j))

end SubexponentialSAT.Subexp.GlobalDescriptorOrder

end OAI.Algorithms
