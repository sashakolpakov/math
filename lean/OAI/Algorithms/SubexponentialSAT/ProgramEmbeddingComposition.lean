import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpProcedureCompose
import OAI.Algorithms.SubexponentialSAT.ExecWorklistLoopBounded

namespace OAI.Algorithms

/-!
# Composition of physical port embeddings

These lemmas transport actual finite-program traces through nested register
and stack placements. State functions describe the placement only; all
executed instructions come from the already verified finite-table relocation.
-/

namespace SubexponentialSAT.ProgramEmbeddingComposition

open BitProgram StructuredCalls

theorem extend_nested {α β γ δ : Type*} (outer : β → γ) (inner : α → β)
    (ho : Function.Injective outer) (hi : Function.Injective inner)
    (frame : γ → δ) (data : α → δ) :
    Function.extend outer (Function.extend inner data (frame ∘ outer)) frame =
      Function.extend (outer ∘ inner) data frame := by
  funext x
  by_cases hout : ∃ y, outer y = x
  · obtain ⟨y, rfl⟩ := hout
    rw [ho.extend_apply]
    by_cases hin : ∃ z, inner z = y
    · obtain ⟨z, rfl⟩ := hin
      rw [hi.extend_apply]
      exact ((ho.comp hi).extend_apply data frame z).symm
    · rw [Function.extend_apply' data (frame ∘ outer) y hin]
      have hcomp : ¬ ∃ z, (outer ∘ inner) z = outer y := by
        rintro ⟨z, hz⟩
        exact hin ⟨z, ho hz⟩
      rw [Function.extend_apply' data frame (outer y) hcomp]
      rfl
  · have hcomp : ¬ ∃ z, (outer ∘ inner) z = x := by
      rintro ⟨z, hz⟩
      exact hout ⟨inner z, hz⟩
    rw [Function.extend_apply' _ frame x hout, Function.extend_apply' data frame x hcomp]

theorem embed_nested {r s R S T U : ℕ}
    (outerR : Fin R → Fin T) (outerS : Fin S → Fin U)
    (innerR : Fin r → Fin R) (innerS : Fin s → Fin S)
    (hor : Function.Injective outerR) (hos : Function.Injective outerS)
    (hir : Function.Injective innerR) (his : Function.Injective innerS)
    (frame : State T U) (data : State r s) :
    embedState outerR outerS frame
        (embedState innerR innerS (projectState outerR outerS frame) data) =
      embedState (outerR ∘ innerR) (outerS ∘ innerS) frame data := by
  apply congrArg₂ StructuredProgram.State.mk
  · exact extend_nested outerR innerR hor hir frame.regs data.regs
  · exact extend_nested outerS innerS hos his frame.stacks data.stacks

theorem project_nested {r s R S T U : ℕ}
    (outerR : Fin R → Fin T) (outerS : Fin S → Fin U)
    (innerR : Fin r → Fin R) (innerS : Fin s → Fin S)
    (hor : Function.Injective outerR) (hos : Function.Injective outerS)
    (hir : Function.Injective innerR) (his : Function.Injective innerS)
    (frame : State T U) (data : State r s) :
    projectState outerR outerS
        (embedState (outerR ∘ innerR) (outerS ∘ innerS) frame data) =
      embedState innerR innerS (projectState outerR outerS frame) data := by
  rw [← embed_nested outerR outerS innerR innerS hor hos hir his frame data]
  exact projectState_embed outerR outerS frame _ hor hos

theorem embed_nested_replace {r s R S T U : ℕ}
    (outerR : Fin R → Fin T) (outerS : Fin S → Fin U)
    (innerR : Fin r → Fin R) (innerS : Fin s → Fin S)
    (hor : Function.Injective outerR) (hos : Function.Injective outerS)
    (hir : Function.Injective innerR) (his : Function.Injective innerS)
    (frame : State T U) (old data : State r s) :
    embedState outerR outerS
        (embedState (outerR ∘ innerR) (outerS ∘ innerS) frame old)
        (embedState innerR innerS (projectState outerR outerS frame) data) =
      embedState (outerR ∘ innerR) (outerS ∘ innerS) frame data := by
  have hd : embedState innerR innerS
      (projectState outerR outerS
        (embedState (outerR ∘ innerR) (outerS ∘ innerS) frame old)) data =
      embedState innerR innerS (projectState outerR outerS frame) data := by
    rw [project_nested outerR outerS innerR innerS hor hos hir his]
    exact SubexpProcedureCompose.embedState_twice innerR innerS hir his _ old data
  rw [← hd, embed_nested outerR outerS innerR innerS hor hos hir his]
  exact SubexpProcedureCompose.embedState_twice (outerR ∘ innerR) (outerS ∘ innerS)
    (hor.comp hir) (hos.comp his) frame old data

/-- The local trace's fixed frame is the projection of the caller frame.
Port relocation executes the same number of instructions and restores every
other caller port. -/
theorem lift_nested_run {r s R S T U labels : ℕ}
    (p : Program R S labels)
    (outerR : Fin R → Fin T) (outerS : Fin S → Fin U)
    (innerR : Fin r → Fin R) (innerS : Fin s → Fin S)
    (hor : Function.Injective outerR) (hos : Function.Injective outerS)
    (hir : Function.Injective innerR) (his : Function.Injective innerS)
    (frame : State T U) (a b : State r s) (bound : ℕ)
    (h : RunsIn p bound
      ((embedState innerR innerS (projectState outerR outerS frame) a).withPC (some p.entry))
      ((embedState innerR innerS (projectState outerR outerS frame) b).withPC none)) :
    RunsIn (ProgramLinking.liftProgram p outerR outerS) bound
      ((embedState (outerR ∘ innerR) (outerS ∘ innerS) frame a).withPC (some p.entry))
      ((embedState (outerR ∘ innerR) (outerS ∘ innerS) frame b).withPC none) := by
  obtain ⟨steps, hsteps, ht⟩ := h
  have ht' : Trace p steps
      ((projectState outerR outerS
        (embedState (outerR ∘ innerR) (outerS ∘ innerS) frame a)).withPC (some p.entry))
      ((embedState innerR innerS (projectState outerR outerS frame) b).withPC none) := by
    rw [project_nested outerR outerS innerR innerS hor hos hir his]
    exact ht
  have he := eval_call_from_state p outerR outerS
    (embedState (outerR ∘ innerR) (outerS ∘ innerS) frame a) hor hos ht'
  rw [embed_nested_replace outerR outerS innerR innerS hor hos hir his] at he
  cases he with
  | call _ htrace => exact ⟨steps, hsteps, htrace⟩

theorem boundedRealizesOn_lift {α : Type*} {R S T U labels : ℕ}
    (p : Program R S labels)
    (outerR : Fin R → Fin T) (outerS : Fin S → Fin U)
    (innerR : Fin 4 → Fin R) (innerS : Fin 5 → Fin S)
    (hor : Function.Injective outerR) (hos : Function.Injective outerS)
    (hir : Function.Injective innerR) (his : Function.Injective innerS)
    (frame : State T U) (enc : α → List Bool) (split : α → Option (α × α))
    (P : α → Prop) (cost : α → ℕ)
    (h : ExecWorklistLoop.Ambient.BoundedRealizesOn p innerR innerS
      (projectState outerR outerS frame) enc split P cost) :
    ExecWorklistLoop.Ambient.BoundedRealizesOn (ProgramLinking.liftProgram p outerR outerS)
      (outerR ∘ innerR) (outerS ∘ innerS) frame enc split P cost := by
  intro x hx pending leaves
  exact lift_nested_run p outerR outerS innerR innerS hor hos hir his frame
    (ExecWorklistLoop.loopData enc ⟨x :: pending, leaves, 0⟩)
    (ExecWorklistLoop.splitData enc x pending leaves (split x)) (cost x)
    (h x hx pending leaves)

end SubexponentialSAT.ProgramEmbeddingComposition

end OAI.Algorithms
