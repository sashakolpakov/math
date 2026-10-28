import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CohomologyTransitions

/-! # Representative Addition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RepresentativeAddition

noncomputable section

/-! Actual global lifts compare the chosen degree-one representatives under addition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem sheafInjectiveCokernelBoundary_exists_lift {X : TopCat.{0}}
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (t : (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence F).X₃.obj.obj (op (⊤ : Opens X)))
    (ht : Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelBoundary F t = 0) :
    ∃ s : (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence F).X₂.obj.obj (op (⊤ : Opens X)),
      (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence F).g.hom.app (op (⊤ : Opens X)) s = t := by
  let S := Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence F
  let x := (CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm t
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact F)
    x (rfl : 0 + 1 = 1) ht
  refine ⟨CategoryTheory.Sheaf.H.equiv₀ S.X₂ isTerminalTop y, ?_⟩
  calc
    _ = CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop (CategoryTheory.Sheaf.H.map S.g 0 y) :=
      CategoryTheory.Sheaf.H.equiv₀_naturality isTerminalTop S.g y
    _ = CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop x := congrArg (CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop) hy
    _ = t := (CategoryTheory.Sheaf.H.equiv₀ S.X₃ isTerminalTop).apply_symm_apply t

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def holomorphicRepresentativeAddDifference (u v : Connecting.holomorphicUnitCohomology E M) :
    (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).X₃.obj.obj (op (⊤ : Opens M)) :=
  CohomologyTransitions.holomorphicCohomologyRepresentative E M (u + v) -
    (CohomologyTransitions.holomorphicCohomologyRepresentative E M u + CohomologyTransitions.holomorphicCohomologyRepresentative E M v)

theorem holomorphicRepresentativeAddDifference_boundary (u v : Connecting.holomorphicUnitCohomology E M) :
    Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelBoundary (Sheaves.holomorphicUnitsSheaf E M) (holomorphicRepresentativeAddDifference E M u v) = 0 := by
  unfold holomorphicRepresentativeAddDifference
  rw [map_sub, map_add, CohomologyTransitions.holomorphicCohomologyRepresentative_spec, CohomologyTransitions.holomorphicCohomologyRepresentative_spec,
    CohomologyTransitions.holomorphicCohomologyRepresentative_spec, sub_self]

theorem exists_holomorphicRepresentativeAddLift (u v : Connecting.holomorphicUnitCohomology E M) :
    ∃ s : (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).X₂.obj.obj (op (⊤ : Opens M)),
      (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).g.hom.app (op (⊤ : Opens M)) s =
        holomorphicRepresentativeAddDifference E M u v :=
  sheafInjectiveCokernelBoundary_exists_lift (Sheaves.holomorphicUnitsSheaf E M) _
    (holomorphicRepresentativeAddDifference_boundary E M u v)

def holomorphicRepresentativeAddLift (u v : Connecting.holomorphicUnitCohomology E M) :
    (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).X₂.obj.obj (op (⊤ : Opens M)) :=
  Classical.choose (exists_holomorphicRepresentativeAddLift E M u v)

theorem holomorphicRepresentativeAddLift_spec (u v : Connecting.holomorphicUnitCohomology E M) :
    (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).g.hom.app (op (⊤ : Opens M))
      (holomorphicRepresentativeAddLift E M u v) = holomorphicRepresentativeAddDifference E M u v :=
  Classical.choose_spec (exists_holomorphicRepresentativeAddLift E M u v)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RepresentativeAddition
