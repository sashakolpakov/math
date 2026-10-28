import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNF

namespace OAI.Algorithms

/-!
# Normalization invariants for the actual child list expressions

The core child is absorbed from the core followed by the retained parent
clauses.  The petal child is absorbed from the filtered petals followed by
the retained parent clauses.  These are the expressions used by the actual
child programs; no reordering equality with another child representation
is required.
-/

namespace SubexponentialSAT.ExecChildNormalizationInvariant

universe u
variable {α : Type u} [DecidableEq α]

def LiteralNodup (F : ExecCNF.Formula α) : Prop :=
  ∀ C ∈ F, C.Nodup

/-- Literal and clause-set uniqueness. Antichain properties are separate. -/
def Normalized (F : ExecCNF.Formula α) : Prop :=
  LiteralNodup F ∧ (F.map ExecCNF.clauseSet).Nodup

def LiteralRange (P : α → Prop) (F : ExecCNF.Formula α) : Prop :=
  ∀ C ∈ F, ∀ x ∈ C, P x

def Subclauses (G F : ExecCNF.Formula α) : Prop :=
  ∀ D ∈ G, ∃ C ∈ F, D.Sublist C

omit [DecidableEq α] in
theorem literalNodup_of_subclauses {G F : ExecCNF.Formula α}
    (hGF : Subclauses G F) (hF : LiteralNodup F) : LiteralNodup G := by
  intro D hD
  obtain ⟨C, hC, hDC⟩ := hGF D hD
  exact hDC.nodup (hF C hC)

omit [DecidableEq α] in
theorem literalRange_of_subclauses {G F : ExecCNF.Formula α} (P : α → Prop)
    (hGF : Subclauses G F) (hF : LiteralRange P F) : LiteralRange P G := by
  intro D hD x hx
  obtain ⟨C, hC, hDC⟩ := hGF D hD
  exact hF C hC x (hDC.subset hx)

omit [DecidableEq α] in
theorem width_of_subclauses {G F : ExecCNF.Formula α} (k : ℕ)
    (hGF : Subclauses G F) (hF : ∀ C ∈ F, C.length ≤ k) :
    ∀ D ∈ G, D.length ≤ k := by
  intro D hD
  obtain ⟨C, hC, hDC⟩ := hGF D hD
  exact hDC.length_le.trans (hF C hC)

theorem eraseClauses_subset (F selected : ExecCNF.Formula α) :
    ExecCNF.eraseClauses F selected ⊆ F := by
  intro C hC
  exact (List.mem_filter.mp hC).1

/-- The mask hypothesis is an actual ordered sublist of a source clause. -/
theorem core_subclauses (F selected : ExecCNF.Formula α) (H : ExecCNF.Clause α)
    (hH : ∃ C ∈ F, H.Sublist C) :
    Subclauses (ExecCNF.absorb (H :: ExecCNF.eraseClauses F selected)) F := by
  intro D hD
  have hm := ExecCNF.absorb_subset _ hD
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hH
  · exact ⟨D, eraseClauses_subset F selected hm, List.Sublist.refl D⟩

/-- Each filtered petal remains a sublist of its selected source clause. -/
theorem petal_subclauses (F selected : ExecCNF.Formula α) (H : ExecCNF.Clause α)
    (hselected : selected ⊆ F) :
    Subclauses
      (ExecCNF.absorb
        (selected.map (fun C => C.filter (fun x => !decide (x ∈ H))) ++
          ExecCNF.eraseClauses F selected)) F := by
  intro D hD
  have hm := ExecCNF.absorb_subset _ hD
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hm
    exact ⟨C, hselected hC, List.filter_sublist⟩
  · exact ⟨D, eraseClauses_subset F selected hm, List.Sublist.refl D⟩

theorem core_normalized (F selected : ExecCNF.Formula α) (H : ExecCNF.Clause α)
    (hF : LiteralNodup F) (hH : ∃ C ∈ F, H.Sublist C) :
    Normalized (ExecCNF.absorb (H :: ExecCNF.eraseClauses F selected)) :=
  ⟨literalNodup_of_subclauses (core_subclauses F selected H hH) hF,
    ExecCNF.absorb_map_nodup _⟩

theorem petal_normalized (F selected : ExecCNF.Formula α) (H : ExecCNF.Clause α)
    (hF : LiteralNodup F) (hselected : selected ⊆ F) :
    Normalized
      (ExecCNF.absorb
        (selected.map (fun C => C.filter (fun x => !decide (x ∈ H))) ++
          ExecCNF.eraseClauses F selected)) :=
  ⟨literalNodup_of_subclauses (petal_subclauses F selected H hselected) hF,
    ExecCNF.absorb_map_nodup _⟩

theorem core_literalRange (P : α → Prop)
    (F selected : ExecCNF.Formula α) (H : ExecCNF.Clause α)
    (hF : LiteralRange P F) (hH : ∃ C ∈ F, H.Sublist C) :
    LiteralRange P (ExecCNF.absorb (H :: ExecCNF.eraseClauses F selected)) :=
  literalRange_of_subclauses P (core_subclauses F selected H hH) hF

theorem petal_literalRange (P : α → Prop)
    (F selected : ExecCNF.Formula α) (H : ExecCNF.Clause α)
    (hF : LiteralRange P F) (hselected : selected ⊆ F) :
    LiteralRange P
      (ExecCNF.absorb
        (selected.map (fun C => C.filter (fun x => !decide (x ∈ H))) ++
          ExecCNF.eraseClauses F selected)) :=
  literalRange_of_subclauses P (petal_subclauses F selected H hselected) hF

theorem core_width (k : ℕ) (F selected : ExecCNF.Formula α) (H : ExecCNF.Clause α)
    (hF : ∀ C ∈ F, C.length ≤ k) (hH : ∃ C ∈ F, H.Sublist C) :
    ∀ D ∈ ExecCNF.absorb (H :: ExecCNF.eraseClauses F selected), D.length ≤ k :=
  width_of_subclauses k (core_subclauses F selected H hH) hF

theorem petal_width (k : ℕ) (F selected : ExecCNF.Formula α) (H : ExecCNF.Clause α)
    (hF : ∀ C ∈ F, C.length ≤ k) (hselected : selected ⊆ F) :
    ∀ D ∈ ExecCNF.absorb
      (selected.map (fun C => C.filter (fun x => !decide (x ∈ H))) ++
        ExecCNF.eraseClauses F selected), D.length ≤ k :=
  width_of_subclauses k (petal_subclauses F selected H hselected) hF

/-- Source normalization, a selected subfamily, and an ordered mask subclause
are sufficient for both actual child expressions. -/
theorem children_preserve (P : α → Prop)
    (F selected : ExecCNF.Formula α) (H : ExecCNF.Clause α)
    (hF : Normalized F) (hrange : LiteralRange P F)
    (hselected : selected ⊆ F) (hH : ∃ C ∈ F, H.Sublist C) :
    Normalized (ExecCNF.absorb (H :: ExecCNF.eraseClauses F selected)) ∧
      LiteralRange P (ExecCNF.absorb (H :: ExecCNF.eraseClauses F selected)) ∧
      Normalized
        (ExecCNF.absorb
          (selected.map (fun C => C.filter (fun x => !decide (x ∈ H))) ++
            ExecCNF.eraseClauses F selected)) ∧
      LiteralRange P
        (ExecCNF.absorb
          (selected.map (fun C => C.filter (fun x => !decide (x ∈ H))) ++
            ExecCNF.eraseClauses F selected)) :=
  ⟨core_normalized F selected H hF.1 hH,
    core_literalRange P F selected H hrange hH,
    petal_normalized F selected H hF.1 hselected,
    petal_literalRange P F selected H hrange hselected⟩

end SubexponentialSAT.ExecChildNormalizationInvariant

end OAI.Algorithms
