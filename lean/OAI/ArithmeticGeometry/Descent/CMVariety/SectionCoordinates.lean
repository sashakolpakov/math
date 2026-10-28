import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

/-! # Section Coordinates -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SectionCoordinates.Abelian

noncomputable section

/-!
Normalize a continuous section in a local product chart by translating
each fiber coordinate by the section's actual coordinate. The base
coordinate stays fixed and the section becomes the zero section.
-/

open Set
open scoped ContDiff

variable {P V X : Type*} [TopologicalSpace P]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [TopologicalSpace X]

def sectionShift (U : Set P) (hU : IsOpen U) (h : P → V) (hh : ContinuousOn h U) :
    OpenPartialHomeomorph (P × V) (P × V) where
  toFun q := (q.1, q.2 - h q.1)
  invFun q := (q.1, q.2 + h q.1)
  source := U ×ˢ univ
  target := U ×ˢ univ
  map_source' := fun _ hq => hq
  map_target' := fun _ hq => hq
  left_inv' := fun q _ => by simp
  right_inv' := fun q _ => by simp
  open_source := hU.prod isOpen_univ
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := continuousOn_fst.prodMk
    (continuousOn_snd.sub (hh.comp continuousOn_fst (fun _ hq => hq.1)))
  continuousOn_invFun := continuousOn_fst.prodMk
    (continuousOn_snd.add (hh.comp continuousOn_fst (fun _ hq => hq.1)))

/-- Translate the section to zero in an actual local product chart,
while preserving the base coordinate exactly. -/
theorem exists_section_normalized_chart
    (e : OpenPartialHomeomorph X (P × V)) (s : P → X)
    (U : Set P) (hU : IsOpen U) (hs : ContinuousOn s U)
    (hsource : ∀ p ∈ U, s p ∈ e.source)
    (hbase : ∀ p ∈ U, (e (s p)).1 = p) :
    ∃ en : OpenPartialHomeomorph X (P × V),
      en.source ⊆ e.source ∧
      (∀ p ∈ U, s p ∈ en.source ∧ en (s p) = (p, 0)) ∧
      ∀ x, (en x).1 = (e x).1 := by
  let h := fun p => (e (s p)).2
  have hh : ContinuousOn h U := (e.continuousOn.comp hs hsource).snd
  let en := e.trans (sectionShift U hU h hh)
  refine ⟨en, fun _ hx => hx.1, ?_, fun _ => rfl⟩
  intro p hp
  constructor
  · refine ⟨hsource p hp, ?_⟩
    change (e (s p)).1 ∈ U ∧ (e (s p)).2 ∈ (univ : Set V)
    exact ⟨(hbase p hp).symm ▸ hp, mem_univ _⟩
  · change ((e (s p)).1, (e (s p)).2 - (e (s ((e (s p)).1))).2) = (p, 0)
    rw [hbase p hp, sub_self]

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Section translation preserves smoothness in both directions. -/
theorem sectionShift_contDiffOn {n : ℕ∞ω} (U : Set E) (hU : IsOpen U)
    (h : E → F) (hh : ContDiffOn ℂ n h U) :
    ContDiffOn ℂ n (sectionShift U hU h hh.continuousOn) (U ×ˢ univ) ∧
      ContDiffOn ℂ n (sectionShift U hU h hh.continuousOn).symm (U ×ˢ univ) := by
  constructor
  · exact contDiffOn_fst.prodMk
      (contDiffOn_snd.sub (hh.comp contDiffOn_fst (fun _ hq => hq.1)))
  · exact contDiffOn_fst.prodMk
      (contDiffOn_snd.add (hh.comp contDiffOn_fst (fun _ hq => hq.1)))

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SectionCoordinates.Abelian
