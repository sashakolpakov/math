import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.FormCompletion
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.DolbeaultZero
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! # Dolbeault Graph -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultGraph

noncomputable section

/-! The closed relation obtained from the actual smooth Dolbeault graph.
Its first projection has dense range. Single-valuedness requires a separate
closability argument and is not part of this construction. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

theorem linearGraphClosure_approximation {A F G : Type*} [AddCommMonoid A] [Module ℂ A]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : A →ₗ[ℂ] F) (g : A →ₗ[ℂ] G)
    (z : (LinearMap.range (f.prod g)).topologicalClosure) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, dist z.val.1 (f a) < ε ∧ dist z.val.2 (g a) < ε := by
  have hz : z.val ∈ closure (Set.range (f.prod g)) := z.property
  obtain ⟨p, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp hz ε hε
  exact ⟨a, max_lt_iff.mp ha⟩

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

def holomorphicDolbeaultGraphMap : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0 →ₗ[ℂ]
    FormCompletion.HolomorphicFormL2 V u 0 × FormCompletion.HolomorphicFormL2 V u 1 :=
  (FormCompletion.holomorphicFormL2Inclusion V u 0).prod
    ((FormCompletion.holomorphicFormL2Inclusion V u 1).comp (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤))

theorem holomorphicDolbeaultGraphMap_apply (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    holomorphicDolbeaultGraphMap V u s = (FormCompletion.holomorphicFormL2Inclusion V u 0 s,
      FormCompletion.holomorphicFormL2Inclusion V u 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ s)) := rfl

theorem holomorphicDolbeaultGraphMap_injective :
    Function.Injective (holomorphicDolbeaultGraphMap V u) := by
  intro a b h
  exact FormCompletion.holomorphicFormL2Inclusion_injective V u 0 (congrArg Prod.fst h)

def holomorphicDolbeaultGraphClosure :
    Submodule ℂ (FormCompletion.HolomorphicFormL2 V u 0 × FormCompletion.HolomorphicFormL2 V u 1) :=
  (LinearMap.range (holomorphicDolbeaultGraphMap V u)).topologicalClosure

abbrev HolomorphicDolbeaultGraph := holomorphicDolbeaultGraphClosure V u

theorem holomorphicDolbeaultGraphClosure_isClosed :
    IsClosed (holomorphicDolbeaultGraphClosure V u :
      Set (FormCompletion.HolomorphicFormL2 V u 0 × FormCompletion.HolomorphicFormL2 V u 1)) :=
  Submodule.isClosed_topologicalClosure _

instance holomorphicDolbeaultGraph_completeSpace :
    CompleteSpace (HolomorphicDolbeaultGraph V u) :=
  inferInstanceAs (CompleteSpace (LinearMap.range (holomorphicDolbeaultGraphMap V u)).topologicalClosure)

def holomorphicDolbeaultGraphInclusion :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0 →ₗ[ℂ] HolomorphicDolbeaultGraph V u :=
  (holomorphicDolbeaultGraphMap V u).codRestrict _ fun s =>
    (LinearMap.range (holomorphicDolbeaultGraphMap V u)).le_topologicalClosure ⟨s, rfl⟩

def holomorphicDolbeaultGraphSource :
    HolomorphicDolbeaultGraph V u →L[ℂ] FormCompletion.HolomorphicFormL2 V u 0 :=
  (ContinuousLinearMap.fst ℂ _ _).comp (holomorphicDolbeaultGraphClosure V u).subtypeL

def holomorphicDolbeaultGraphValue :
    HolomorphicDolbeaultGraph V u →L[ℂ] FormCompletion.HolomorphicFormL2 V u 1 :=
  (ContinuousLinearMap.snd ℂ _ _).comp (holomorphicDolbeaultGraphClosure V u).subtypeL

theorem holomorphicDolbeaultGraphSource_apply (z : HolomorphicDolbeaultGraph V u) :
    holomorphicDolbeaultGraphSource V u z = z.val.1 := rfl

theorem holomorphicDolbeaultGraphValue_apply (z : HolomorphicDolbeaultGraph V u) :
    holomorphicDolbeaultGraphValue V u z = z.val.2 := rfl

theorem holomorphicDolbeaultGraphSource_inclusion (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    holomorphicDolbeaultGraphSource V u (holomorphicDolbeaultGraphInclusion V u s) =
      FormCompletion.holomorphicFormL2Inclusion V u 0 s := rfl

theorem holomorphicDolbeaultGraphValue_inclusion (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) :
    holomorphicDolbeaultGraphValue V u (holomorphicDolbeaultGraphInclusion V u s) =
      FormCompletion.holomorphicFormL2Inclusion V u 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ s) := rfl

theorem holomorphicDolbeaultGraphSource_dense : DenseRange (holomorphicDolbeaultGraphSource V u) := by
  apply (FormCompletion.holomorphicFormL2Inclusion_dense V u 0).mono
  rintro _ ⟨s, rfl⟩
  exact ⟨holomorphicDolbeaultGraphInclusion V u s, rfl⟩

theorem holomorphicDolbeaultGraph_approximation (z : HolomorphicDolbeaultGraph V u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0,
      dist (holomorphicDolbeaultGraphSource V u z) (FormCompletion.holomorphicFormL2Inclusion V u 0 s) < ε ∧
      dist (holomorphicDolbeaultGraphValue V u z)
        (FormCompletion.holomorphicFormL2Inclusion V u 1 (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤ s)) < ε := by
  exact linearGraphClosure_approximation (FormCompletion.holomorphicFormL2Inclusion V u 0)
    ((FormCompletion.holomorphicFormL2Inclusion V u 1).comp (HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero u ⊤)) z ε hε

theorem holomorphicDolbeaultGraph_of_holomorphic (s : HolomorphicSection.Data.HolomorphicLineSection u ⊤) :
    holomorphicDolbeaultGraphValue V u (holomorphicDolbeaultGraphInclusion V u
      (HolomorphicLine.AntiForms.holomorphicLineSectionSmoothZeroForm u ⊤ s)) = 0 := by
  rw [holomorphicDolbeaultGraphValue_inclusion, HolomorphicLine.DolbeaultZero.holomorphicLineDolbeaultZero_of_holomorphic,
    map_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultGraph
