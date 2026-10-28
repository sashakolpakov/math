import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointUnderlying
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Immersion Point Iso -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImmersionPointIso.Constructions

noncomputable section

/-! An actual open immersion into a locally finite-type complex scheme
is an isomorphism if its map on genuine complex points is surjective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem openImmersion_isIso_of_pointSurjective {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Y) [IsOpenImmersion f.left] [LocallyOfFiniteType Y.hom]
    (hf : Function.Surjective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)) : IsIso f.left := by
  classical
  let : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  apply (isIso_iff_isOpenImmersion_and_surjective f.left).mpr
  refine ⟨inferInstance, (surjective_iff f.left).mpr ?_⟩
  intro y
  by_contra hy
  have hne : ((Set.range f.left)ᶜ : Set Y.left).Nonempty := ⟨y, hy⟩
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hne
    f.left.isOpenEmbedding.isOpen_range.isClosed_compl.isLocallyClosed
  let p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y := Over.homMk (pointOfClosedPoint Y.hom z hzc)
    (pointOfClosedPoint_comp Y.hom z hzc)
  have hp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p = z := pointOfClosedPoint_apply Y.hom z hzc _
  obtain ⟨q, hq⟩ := hf p
  apply hz
  refine ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying q, ?_⟩
  exact (congrArg (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p) hq).trans hp

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImmersionPointIso.Constructions
