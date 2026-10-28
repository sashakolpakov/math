import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceTyped

namespace OAI.Algorithms

/-! Exact table shapes and read validity for finite typed interpolation
caches. Flattening is a specification of the arrays produced natively. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.UniversalRowTableSource

variable {C : Type*} {Q : ℕ}

def tables (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) : UniversalRowLoop.Tables :=
  ⟨List.ofFn (fun i => encode (values i)),List.ofFn (fun i => encode (inverse i)),
    List.ofFn (fun i => encode (negative i)),List.ofFn (fun i => List.ofFn (fun j => encode (difference i j)))⟩

private theorem getD_ofFn {A : Type*} (f : Fin Q → A) (default : A) (i : Fin Q) :
    (List.ofFn f).getD i.val default=f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem tables_values (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (i : Fin Q) :
    (tables encode values inverse negative difference).values.getD i.val []=encode (values i) :=
  getD_ofFn _ _ _

theorem tables_inverse (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (i : Fin Q) :
    (tables encode values inverse negative difference).inverses.getD i.val []=encode (inverse i) :=
  getD_ofFn _ _ _

theorem tables_negative (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (i : Fin Q) :
    (tables encode values inverse negative difference).negatives.getD i.val []=encode (negative i) :=
  getD_ofFn _ _ _

theorem tables_difference (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (i j : Fin Q) :
    ((tables encode values inverse negative difference).differences.getD i.val []).getD j.val []=
      encode (difference i j) := by
  change ((List.ofFn (fun i => List.ofFn (fun j => encode (difference i j)))).getD i.val []).getD j.val []=_
  rw [getD_ofFn,getD_ofFn]

private theorem position_lt (s : Finset (Fin Q)) (i : ℕ) (hi : i∈positions s) : i < Q := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
  exact j.isLt

/-- Each native fixed-width read is in range, including the inner row reads.
The validity proof comes from actual finite cache dimensions. -/
theorem tables_valid (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) (width rowWidth : List Bool)
    (hwidth : ∀ c,(encode c).length=width.length)
    (hrow : rowWidth.length=Q*width.length) (s : Finset (Fin Q)) :
    UniversalRowLoop.Valid (tables encode values inverse negative difference) width rowWidth (positions s) := by
  constructor
  · intro word hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hwidth _
  · intro word hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hwidth _
  · intro word hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hwidth _
  · intro word hw
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hxs
    simp only [List.length_flatten,List.map_ofFn,hrow]
    have he : (List.length ∘ fun j => encode (difference i j)) = fun _ : Fin Q => width.length := by
      funext j
      exact hwidth _
    rw [he]
    simp
  · intro i hi
    have h := position_lt s i hi
    simpa only [tables,List.length_ofFn] using And.intro h (And.intro h h)
  · intro i hi word hw
    have hii : i < Q := position_lt s i hi
    change word∈(List.ofFn (fun i => List.ofFn (fun j => encode (difference i j)))).getD i [] at hw
    rw [getD_ofFn _ _ (⟨i,hii⟩:Fin Q)] at hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact hwidth _
  · intro i hi j hj
    have hii : i < Q := position_lt s i hi
    have hjj : j < Q := position_lt s j hj
    change j < ((List.ofFn (fun i => List.ofFn (fun j => encode (difference i j)))).getD i []).length ∧
      j < (List.ofFn (fun i => encode (negative i))).length
    rw [getD_ofFn _ _ (⟨i,hii⟩:Fin Q)]
    simpa using And.intro hjj hjj

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
