import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedGraphRelation

/-! # Intrinsic Indexed Graphs -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicIndexedGraphs.CM

noncomputable section

/-! The native geometric frame determines its full Siegel graph and
its lower coordinates after any finite reindexing and the required
position/momentum swap. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Adelic.BallNatural

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)
  {I : Type} [Fintype I] (e : I ≃ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)

def nativeIndexedPeriod (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I :=
  ReindexTheta.CM.siegelReindex e.symm ((RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P).period z)

def nativeIndexedFrame (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) : Matrix I I ℂ :=
  ((RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P).frame z).val.submatrix e e

theorem native_indexed_frame_det [DecidableEq I] (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    (nativeIndexedFrame A P e z).det = (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P).halfFrame z ^ 2 :=
  (Matrix.det_submatrix_equiv_self e _).trans
    (((RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry A P).2.2.2.2.2.1 z).2.symm)

theorem native_indexed_graph_equation (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (α : (I ⊕ I) → ℂ)
    (u : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ)
    (h : (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P).complexPhase
      (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => α ((e.sumCongr e).symm i))) = RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z u) :
    (nativeIndexedPeriod A P e z).matrix.mulVec (fun i => α (.inr i)) = fun i => α (.inl i) := by
  let N := RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P
  let t := (N.frame z).val.mulVec u
  have hg : N.complexPhase (Sum.elim t ((N.period z).matrix.mulVec t)) = RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z u :=
    (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry A P).2.2.2.2.2.2.1 z u
  exact IndexedGraphRelation.CM.reindexed_swapped_graph_equation e (N.period z).matrix α t
    (N.complexPhase.injective (h.trans hg.symm))

omit [Fintype I] in
theorem native_indexed_graph_bottom (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (α : (I ⊕ I) → ℂ)
    (u : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ)
    (h : (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P).complexPhase
      (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => α ((e.sumCongr e).symm i))) = RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z u) :
    (fun i => α (.inr i)) = fun i => ((RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P).frame z).val.mulVec u (e i) := by
  let N := RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P
  let t := (N.frame z).val.mulVec u
  have hg : N.complexPhase (Sum.elim t ((N.period z).matrix.mulVec t)) = RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame A z u :=
    (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry A P).2.2.2.2.2.2.1 z u
  have hp := N.complexPhase.injective (h.trans hg.symm)
  funext i
  have he := congrFun hp (.inl (e i))
  change α (.inr (e.symm (e i))) = t (e i) at he
  simpa only [Equiv.symm_apply_apply] using! he

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicIndexedGraphs.CM
