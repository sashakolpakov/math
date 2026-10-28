import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DegreeAdjointIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ClosedDolbeaultOperator
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiOneHilbert

/-! # Closed Dolbeault One -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ClosedDolbeaultOne

noncomputable section

/-! The actual densely defined closed Dolbeault operator from antiholomorphic one-forms. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] NormedSpace.complexToReal

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)

def holomorphicDolbeaultOneGraphMap : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ]
    AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2 :=
  (AntiOneHilbert.holomorphicAntiOneL2Inclusion V u).prod
    ((FormCompletion.holomorphicFormL2Inclusion V u 2).comp
      ((HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u ⊤ 2).subtype.comp (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1)))

def holomorphicDolbeaultOneGraphClosure :
    Submodule ℂ (AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2) :=
  (LinearMap.range (holomorphicDolbeaultOneGraphMap V u)).topologicalClosure

theorem holomorphicDolbeaultOneGraphClosure_isClosed :
    IsClosed (holomorphicDolbeaultOneGraphClosure V u :
      Set (AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2)) :=
  Submodule.isClosed_topologicalClosure _

theorem holomorphicDolbeaultOneGraphMap_pair (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 2) :
    inner ℂ (holomorphicDolbeaultOneGraphMap V u a).2 (FormCompletion.holomorphicFormL2Inclusion V u 2 b) =
      inner ℂ (holomorphicDolbeaultOneGraphMap V u a).1.val
        (FormCompletion.holomorphicFormL2Inclusion V u 1 (DegreeCodifferential.holomorphicLineDegreeCodifferential V u 1 b)) := by
  calc
    _ = FormIntegralPair.holomorphicLineFormIntegralPair V u 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val b :=
      FormCompletion.holomorphicFormL2Inclusion_inner V u 2 _ _
    _ = FormIntegralPair.holomorphicLineFormIntegralPair V u 1 a.val (DegreeCodifferential.holomorphicLineDegreeCodifferential V u 1 b) :=
      DegreeAdjointIntegral.holomorphicLineDegreeCodifferential_pair_right V u 1 a b
    _ = _ := (FormCompletion.holomorphicFormL2Inclusion_inner V u 1 _ _).symm

theorem holomorphicDolbeaultOneGraphClosure_pair
    (z : AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2)
    (hz : z ∈ holomorphicDolbeaultOneGraphClosure V u) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 2) :
    inner ℂ z.2 (FormCompletion.holomorphicFormL2Inclusion V u 2 b) =
      inner ℂ z.1.val (FormCompletion.holomorphicFormL2Inclusion V u 1 (DegreeCodifferential.holomorphicLineDegreeCodifferential V u 1 b)) := by
  let S : Set (AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2) :=
    {w | inner ℂ w.2 (FormCompletion.holomorphicFormL2Inclusion V u 2 b) =
      inner ℂ w.1.val (FormCompletion.holomorphicFormL2Inclusion V u 1 (DegreeCodifferential.holomorphicLineDegreeCodifferential V u 1 b))}
  have hS : IsClosed S := isClosed_eq (continuous_snd.inner continuous_const)
    ((continuous_subtype_val.comp continuous_fst).inner continuous_const)
  have hs : Set.range (holomorphicDolbeaultOneGraphMap V u) ⊆ S := by
    rintro _ ⟨a, rfl⟩
    exact holomorphicDolbeaultOneGraphMap_pair V u a b
  exact closure_minimal hs hS hz

theorem holomorphicDolbeaultOneGraphClosure_zero_source
    (z : AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2)
    (hz : z ∈ holomorphicDolbeaultOneGraphClosure V u) (hs : z.1 = 0) : z.2 = 0 := by
  apply DolbeaultClosable.inner_zero_of_denseRange (FormCompletion.holomorphicFormL2Inclusion V u 2) (FormCompletion.holomorphicFormL2Inclusion_dense V u 2)
  intro b
  rw [holomorphicDolbeaultOneGraphClosure_pair V u z hz b, hs]
  exact inner_zero_left _

def holomorphicClosedDolbeaultOne : AntiOneHilbert.HolomorphicAntiOneL2 V u →ₗ.[ℂ] FormCompletion.HolomorphicFormL2 V u 2 :=
  (holomorphicDolbeaultOneGraphClosure V u).toLinearPMap

theorem holomorphicClosedDolbeaultOne_graph :
    (holomorphicClosedDolbeaultOne V u).graph = holomorphicDolbeaultOneGraphClosure V u :=
  Submodule.toLinearPMap_graph_eq _ (holomorphicDolbeaultOneGraphClosure_zero_source V u)

theorem holomorphicClosedDolbeaultOne_isClosed : (holomorphicClosedDolbeaultOne V u).IsClosed :=
  Eq.mpr (congrArg (fun S : Submodule ℂ (AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2) =>
    IsClosed (S : Set (AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2)))
      (holomorphicClosedDolbeaultOne_graph V u)) (holomorphicDolbeaultOneGraphClosure_isClosed V u)

theorem holomorphicClosedDolbeaultOne_mem_graph
    (z : AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2)
    (hz : z ∈ holomorphicDolbeaultOneGraphClosure V u) : z ∈ (holomorphicClosedDolbeaultOne V u).graph :=
  Eq.mpr (congrArg (fun S : Submodule ℂ (AntiOneHilbert.HolomorphicAntiOneL2 V u × FormCompletion.HolomorphicFormL2 V u 2) => z ∈ S)
    (holomorphicClosedDolbeaultOne_graph V u)) hz

theorem holomorphicClosedDolbeaultOne_smooth_graph (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    (AntiOneHilbert.holomorphicAntiOneL2Inclusion V u a, FormCompletion.holomorphicFormL2Inclusion V u 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val) ∈
      (holomorphicClosedDolbeaultOne V u).graph :=
  holomorphicClosedDolbeaultOne_mem_graph V u _
    ((LinearMap.range (holomorphicDolbeaultOneGraphMap V u)).le_topologicalClosure ⟨a, rfl⟩)

theorem holomorphicClosedDolbeaultOne_smooth_mem (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    AntiOneHilbert.holomorphicAntiOneL2Inclusion V u a ∈ (holomorphicClosedDolbeaultOne V u).domain :=
  LinearPMap.mem_domain_of_mem_graph (holomorphicClosedDolbeaultOne_smooth_graph V u a)

def holomorphicClosedDolbeaultOneSmoothInclusion :
    HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ] (holomorphicClosedDolbeaultOne V u).domain :=
  (AntiOneHilbert.holomorphicAntiOneL2Inclusion V u).codRestrict _ (holomorphicClosedDolbeaultOne_smooth_mem V u)

theorem holomorphicClosedDolbeaultOne_smooth_apply (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    holomorphicClosedDolbeaultOne V u (holomorphicClosedDolbeaultOneSmoothInclusion V u a) =
      FormCompletion.holomorphicFormL2Inclusion V u 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val :=
  (holomorphicClosedDolbeaultOne V u).mem_graph_snd_inj
    ((holomorphicClosedDolbeaultOne V u).mem_graph (holomorphicClosedDolbeaultOneSmoothInclusion V u a))
    (holomorphicClosedDolbeaultOne_smooth_graph V u a) rfl

theorem holomorphicClosedDolbeaultOne_domain_dense :
    Dense ((holomorphicClosedDolbeaultOne V u).domain : Set (AntiOneHilbert.HolomorphicAntiOneL2 V u)) := by
  apply (AntiOneHilbert.holomorphicAntiOneL2Inclusion_dense V u).mono
  rintro _ ⟨a, rfl⟩
  exact holomorphicClosedDolbeaultOne_smooth_mem V u a

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ClosedDolbeaultOne
