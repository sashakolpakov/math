import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.QuarticSearch

namespace OAI.Algorithms

/-!
# Duplicate-free executable coefficient enumeration

These proofs concern the explicit lists used by `QuarticSearch`; they do not
replace the lists by an abstract enumeration of a finite type.
-/

namespace SubexponentialSAT.SubexpVectorEnumeration

/-- The increasing residue representatives contain no duplicates, including
for a composite or zero modulus. -/
theorem elements_nodup (p : ℕ) : (QuarticSearch.elements p).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  apply Fin.ext
  have hval := congrArg ZMod.val hij
  simpa only [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] using hval

/-- Prefixing different alphabet entries gives disjoint blocks, while
prefixing one entry preserves the distinctness of the shorter vectors. -/
theorem vectors_nodup {A : Type*} (alphabet : List A)
    (h : alphabet.Nodup) (d : ℕ) : (QuarticSearch.vectors alphabet d).Nodup := by
  induction d with
  | zero => simp [QuarticSearch.vectors]
  | succ d ih =>
      rw [QuarticSearch.vectors]
      apply List.nodup_flatMap.mpr
      refine ⟨fun a _ => ih.map (fun u v huv => ?_), ?_⟩
      · funext i
        exact congrFun huv i.succ
      · exact h.imp fun {a b} hab x hx hy => by
          rcases List.mem_map.mp hx with ⟨v, _, rfl⟩
          rcases List.mem_map.mp hy with ⟨w, _, hw⟩
          exact hab (Fin.cons_inj.mp hw).1.symm

/-- In particular the actual residue-vector search list is duplicate-free. -/
theorem allVectors_nodup (p d : ℕ) :
    (QuarticSearch.vectors (QuarticSearch.elements p) d).Nodup :=
  vectors_nodup _ (elements_nodup p) d

end SubexponentialSAT.SubexpVectorEnumeration

end OAI.Algorithms
