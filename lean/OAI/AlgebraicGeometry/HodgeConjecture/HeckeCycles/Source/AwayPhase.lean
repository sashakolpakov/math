import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SplittingProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoordinateBlockMatrix
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalBlockConjugation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.LocalProductBlocks
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockFixedPhase

/-! # Away Phase -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.AwayPhase.CM

noncomputable section

/-! Every element of the actual original source away group fixes the
active finite phase vectors in the constructed coordinate frame. -/

open scoped Classical _root_.Matrix _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.WeilData.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

theorem project_conjugation {I M : Type*} [Fintype I] [DecidableEq I] [Group M]
    (q : ℕ) [Fact q.Prime] (p : M →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (u m : M) (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ_[q])
    (hu : p u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S) (A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hm : p m = A) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom (p (u * m * u⁻¹)) =
      S * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom A * S⁻¹ := by
  simp only [map_mul, map_inv, hu, hm, RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion_projection]

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga : Type} [Group Ga] [TopologicalSpace Ga]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga
    (WeilData.CM.RealCoverGroup E places) (WeilData.CM.FiniteCoverGroup E places) (WeilData.CM.AdelicCoverGroup E places))
  (hb : D.pel.reference.b = B.b) (hweil : D.weil = WeilData.CM.weilData E places)
  {n : ℕ} (c : GeometricSource.CM.Positions E places ≃ Fin n)

include hb hweil c in
theorem fixes (u : WeilData.CM.FiniteCoverGroup E places)
    (hu : FixedFrameAuxiliaryFamily.CM.Family.CoordinateIdentity E D (ComplexAction.CM.Symplectic.frame E L.coordinates) u)
    (w : FactorTheta.CM.RationalWeilFactorization.Away E L
      (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (D.pel.reference.distinguished, false)))
    (p t : Fin 3 → ℚ_[q]) :
    ((WeilData.CM.weilData E places).finite.project
      (u * FactorTheta.CM.RationalWeilFactorization.splitting E L
        (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (D.pel.reference.distinguished, false)) (1, w) * u⁻¹)).val *ᵥ
      Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
        (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t) =
      Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
        (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t) := by
  have hs := CoordinateBlockMatrix.CM.exists_matrix E L.coordinates D hb c u hu
  let S := Classical.choose hs
  have hS := (Classical.choose_spec hs).1
  have hr := (Classical.choose_spec hs).2
  let f := CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (D.pel.reference.distinguished, false)
  let τ := fun i => CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (i, false)
  have hSu : (WeilData.CM.weilData E places).finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S :=
    (congrArg (fun W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) (WeilData.CM.RealCoverGroup E places)
      (WeilData.CM.FiniteCoverGroup E places) (WeilData.CM.AdelicCoverGroup E places) => W.finite.project u) hweil).symm.trans hS
  have hA : (WeilData.CM.weilData E places).finite.project (FactorTheta.CM.RationalWeilFactorization.splitting E L f (1, w)) =
      ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
        (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (1, w)) :=
    SplittingProjection.CM.projection E L f 1 w
  have hp := (project_conjugation q (WeilData.CM.weilData E places).finite.project u
    (FactorTheta.CM.RationalWeilFactorization.splitting E L f (1, w)) S hSu _ hA).trans
      (LocalBlockConjugation.CM.conjugation E L f τ c S hr (1, w))
  exact BlockFixedPhase.CM.finite_fixed q c D.pel.reference.distinguished _
    (SourceFinite.LocalBlocks.CM.blocks E f L τ (1, w))
    (LocalProductBlocks.CM.assemble E f L 1 w) hp p t

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.AwayPhase.CM
