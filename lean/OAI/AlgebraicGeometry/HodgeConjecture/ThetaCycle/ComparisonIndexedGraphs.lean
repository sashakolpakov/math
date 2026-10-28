import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicIndexedGraphs

/-! # Comparison Indexed Graphs -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonIndexedGraphs.CM

noncomputable section

/-! The full geometry proposition identifies the actual Siegel graph for
any native comparison witness, with the same reindexing and phase swap. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallNatural

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W}
  (C : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H W A) (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification C)
  {I : Type} [Fintype I] (e : I ≃ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)

def comparisonIndexedPeriod (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I :=
  ReindexTheta.CM.siegelReindex e.symm (C.period z)

def comparisonIndexedFrame (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) : Matrix I I ℂ :=
  (C.frame z).val.submatrix e e

include hG in
theorem comparison_indexed_frame_det [DecidableEq I] (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    (comparisonIndexedFrame C e z).det = C.halfFrame z ^ 2 :=
  (Matrix.det_submatrix_equiv_self e _).trans ((hG.2.2.2.2.2.1 z).2.symm)

include hG in
theorem comparison_indexed_graph_equation (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (α : (I ⊕ I) → ℂ)
    (u : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ)
    (h : C.complexPhase (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => α ((e.sumCongr e).symm i))) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z u) :
    (comparisonIndexedPeriod C e z).matrix.mulVec (fun i => α (.inr i)) =
      fun i => α (.inl i) := by
  let t := (C.frame z).val.mulVec u
  have hg : C.complexPhase (Sum.elim t ((C.period z).matrix.mulVec t)) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z u := hG.2.2.2.2.2.2.1 z u
  exact IndexedGraphRelation.CM.reindexed_swapped_graph_equation e (C.period z).matrix α t
    (C.complexPhase.injective (h.trans hg.symm))

include hG in
omit [Fintype I] in
theorem comparison_indexed_graph_bottom (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (α : (I ⊕ I) → ℂ)
    (u : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ)
    (h : C.complexPhase (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => α ((e.sumCongr e).symm i))) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z u) :
    (fun i => α (.inr i)) = fun i => (C.frame z).val.mulVec u (e i) := by
  let t := (C.frame z).val.mulVec u
  have hg : C.complexPhase (Sum.elim t ((C.period z).matrix.mulVec t)) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z u := hG.2.2.2.2.2.2.1 z u
  have hp := C.complexPhase.injective (h.trans hg.symm)
  funext i
  have he := congrFun hp (.inl (e i))
  change α (.inr (e.symm (e i))) = t (e i) at he
  simpa only [Equiv.symm_apply_apply] using! he

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonIndexedGraphs.CM
