import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentEnumeration

namespace OAI.Algorithms

/-! Explicit row and column lists for the local matrix searches. -/

namespace SubexponentialSAT.Subexp.FiberEnumeration

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.AssignmentEnumeration

section Subtype

variable {α : Type*}

/-- Filter an explicit list and retain the checked predicate proofs. -/
def subtypeList (p : α → Prop) [DecidablePred p] (xs : List α) : List {a // p a} :=
  (xs.filter (fun a => decide (p a))).attach.map
    (fun a => ⟨a.val, by
      have h : decide (p a.val) = true := (List.mem_filter.mp a.property).2
      exact of_decide_eq_true h⟩)

theorem subtypeList_nodup (p : α → Prop) [DecidablePred p] (xs : List α)
    (hn : xs.Nodup) : (subtypeList p xs).Nodup := by
  unfold subtypeList
  apply (List.nodup_attach.mpr (hn.filter _)).map
  intro a b h
  exact Subtype.ext (congrArg (fun x : {a // p a} => x.val) h)

theorem mem_subtypeList (p : α → Prop) [DecidablePred p] (xs : List α)
    (a : {x // p x}) (ha : a.val ∈ xs) : a ∈ subtypeList p xs := by
  unfold subtypeList
  apply List.mem_map.mpr
  let b : {x // x ∈ xs.filter (fun x => decide (p x))} :=
    ⟨a.val, List.mem_filter.mpr ⟨ha, by simpa using a.property⟩⟩
  exact ⟨b, List.mem_attach _ _, Subtype.ext rfl⟩

end Subtype

variable {r Q Δ : ℕ}

def sideList (t : Fin Q) (g : Fin r) : List (Side (Δ := Δ) t g) :=
  subtypeList (fun u => u ∈ side (Δ := Δ) t g) (universalAlphabet r Q Δ)

theorem sideList_nodup (t : Fin Q) (g : Fin r) :
    (sideList (Δ := Δ) t g).Nodup :=
  subtypeList_nodup _ _ (universalAlphabet_nodup r Q Δ)

theorem mem_sideList (t : Fin Q) (g : Fin r) (u : Side (Δ := Δ) t g) :
    u ∈ sideList t g :=
  mem_subtypeList _ _ u (mem_universalAlphabet r Q Δ u.val)

def jointList (t : Fin Q) (g : Fin r) (i : Fin Δ) : List (Joint t g i) :=
  subtypeList (fun u => u ∈ joint t g i) (universalAlphabet r Q Δ)

theorem jointList_nodup (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    (jointList t g i).Nodup :=
  subtypeList_nodup _ _ (universalAlphabet_nodup r Q Δ)

theorem mem_jointList (t : Fin Q) (g : Fin r) (i : Fin Δ) (u : Joint t g i) :
    u ∈ jointList t g i :=
  mem_subtypeList _ _ u (mem_universalAlphabet r Q Δ u.val)

/-- Stack every slot's joint rows, in increasing slot order. -/
def rowList (t : Fin Q) (g : Fin r) : List ((i : Fin Δ) × Joint t g i) :=
  (List.finRange Δ).sigma (jointList t g)

theorem rowList_nodup (t : Fin Q) (g : Fin r) :
    (rowList (Δ := Δ) t g).Nodup :=
  (List.nodup_finRange Δ).sigma (jointList_nodup t g)

theorem mem_rowList (t : Fin Q) (g : Fin r) (u : (i : Fin Δ) × Joint t g i) :
    u ∈ rowList t g :=
  List.mem_sigma.mpr ⟨List.mem_finRange u.1, mem_jointList t g u.1 u.2⟩

/-- The forward map is `get`; the inverse is `idxOf` in the filtered list. -/
def sideEquiv (t : Fin Q) (g : Fin r) :
    Fin (sideList (Δ := Δ) t g).length ≃ Side (Δ := Δ) t g :=
  List.Nodup.getEquivOfForallMemList _ (sideList_nodup t g) (mem_sideList t g)

def rowEquiv (t : Fin Q) (g : Fin r) :
    Fin (rowList (Δ := Δ) t g).length ≃ ((i : Fin Δ) × Joint t g i) :=
  List.Nodup.getEquivOfForallMemList _ (rowList_nodup t g) (mem_rowList t g)

theorem sideList_length_card (t : Fin Q) (g : Fin r) :
    (sideList (Δ := Δ) t g).length = Fintype.card (Side (Δ := Δ) t g) :=
  enumeration_length _ (sideList_nodup t g) (mem_sideList t g)

theorem rowList_length_card (t : Fin Q) (g : Fin r) :
    (rowList (Δ := Δ) t g).length = Fintype.card ((i : Fin Δ) × Joint t g i) :=
  enumeration_length _ (rowList_nodup t g) (mem_rowList t g)

end SubexponentialSAT.Subexp.FiberEnumeration

end OAI.Algorithms
