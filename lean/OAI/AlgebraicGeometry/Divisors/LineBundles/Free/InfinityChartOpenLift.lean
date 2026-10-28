import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveInfinityChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelativeBaseChangeChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackIso

/-! # Infinity Chart Open Lift -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free

noncomputable section

/-! A free infinity chart contained over an open base lifts to a
genuine free infinity chart of the actual projective pullback. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X U : Scheme.{0}} {p : E ⟶ X} {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E}
    (i : U ⟶ X) [IsOpenImmersion i] (x : U)
    (C : ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart p L (i x)) (hc : Set.range C.baseMap ⊆ Set.range i)

def ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart.openLift :
    ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart (pullback.snd p i) (L.pullback (pullback.fst p i)) x := by
  let a := IsOpenImmersion.lift i C.baseMap hc
  have ha : a ≫ i = C.baseMap := IsOpenImmersion.lift_fac i C.baseMap hc
  let : IsOpenImmersion (a ≫ i) := ha.symm ▸ C.open_base
  let : IsOpenImmersion a := IsOpenImmersion.of_comp a i
  let q := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase C.coefficient (C.coefficient × C.module)
  let j := Open.RelativeBaseChangeChart.BundleCycles.openRelativeChartLift p q C.baseMap C.totalMap C.square i a ha
  exact {
    coefficient := C.coefficient
    module := C.module
    rank := C.rank
    basis := C.basis
    baseMap := a
    totalMap := j
    open_base := inferInstance
    open_total := inferInstance
    contains := by
      obtain ⟨u, hu⟩ := C.contains
      refine ⟨u, i.isOpenEmbedding.injective ?_⟩
      exact (congrArg (fun k : Spec C.coefficient ⟶ X => k u) ha).trans hu
    square := Open.RelativeBaseChangeChart.BundleCycles.openRelativeChartLift_isPullback p q C.baseMap C.totalMap C.square i a ha
    idealIso := LineBundle.PullbackIso.Cycles.lineBundlePullbackCompIso L j (pullback.fst p i) ≪≫
      LineBundle.PullbackIso.Cycles.lineBundlePullbackCongrIso L (Open.RelativeBaseChangeChart.BundleCycles.openRelativeChartLift_fst p q C.baseMap C.totalMap C.square i a ha) ≪≫
      C.idealIso }

theorem ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart.openLift_rank : (C.openLift i x hc).rank = C.rank := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free
