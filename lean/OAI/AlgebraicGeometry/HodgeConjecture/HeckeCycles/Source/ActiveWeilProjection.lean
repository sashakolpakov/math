import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.CoordinateBlockMatrix
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SplittingProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicFilledPEL

/-! # Active Weil Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveWeilProjection.CM

noncomputable section

/-! The literal original source active Weil lift has the exact
finite projection required by the same-character radial argument. -/

open scoped Classical _root_.Matrix _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.WeilData.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

theorem recover {G : Type*} [Group G] (u a b : G) (h : u * a * u⁻¹ = b) : a = u⁻¹ * b * u := by
  rw [← h]
  group

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga : Type} [Group Ga] [TopologicalSpace Ga]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga
    (WeilData.CM.RealCoverGroup E places) (WeilData.CM.FiniteCoverGroup E places) (WeilData.CM.AdelicCoverGroup E places))
  (hb : D.pel.reference.b = B.b) (hweil : D.weil = WeilData.CM.weilData E places)
  (hq : D.pel.IsGoodCompletelySplitPrime) {n : ℕ} (c : GeometricSource.CM.Positions E places ≃ Fin n)

include hb hweil hq in
theorem projection (u : WeilData.CM.FiniteCoverGroup E places)
    (hu : FixedFrameAuxiliaryFamily.CM.Family.CoordinateIdentity E D (ComplexAction.CM.Symplectic.frame E L.coordinates) u)
    (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    (WeilData.CM.weilData E places).finite.project (FactorTheta.CM.RationalWeilFactorization.splitting E L
      (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (D.pel.reference.distinguished, false)) (g, 1)) =
      ((WeilData.CM.weilData E places).finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (CMExtraction.ActiveBlockMatrices.Local.activeBlockGL c D.pel.reference.distinguished (CMExtraction.Contragredient.Local.contragredient ℚ_[q] g))) *
            (WeilData.CM.weilData E places).finite.project u := by
  have hs := CoordinateBlockMatrix.CM.exists_matrix E L.coordinates D hb c u hu
  let S := Classical.choose hs
  have hS := (Classical.choose_spec hs).1
  have hr := (Classical.choose_spec hs).2
  let μ := D.pel.reference.distinguished
  let τ := fun i => CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel (i, false)
  have hτ : ∀ i, i ≠ μ → QadicPlace.CM.place E (τ i) ≠ QadicPlace.CM.place E (τ μ) := by
    intro i hi he
    exact hi ((PairedPlaceFibers.CM.fiber E (OppositeCoordinates.CM.coordinates E L.coordinates)
      (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel) (IntrinsicFilledPEL.CM.Intrinsic.labels_injective E D.pel hq)
      (CMExtraction.GaloisDiscrete.ParameterChoices.nativeFieldEmbedding_conjugate D.pel hq) (i, false) (μ, false)).mp he)
  have hSu : (WeilData.CM.weilData E places).finite.project u = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S :=
    (congrArg (fun W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) (WeilData.CM.RealCoverGroup E places)
      (WeilData.CM.FiniteCoverGroup E places) (WeilData.CM.AdelicCoverGroup E places) => W.finite.project u) hweil).symm.trans hS
  have hA : (WeilData.CM.weilData E places).finite.project (FactorTheta.CM.RationalWeilFactorization.splitting E L (τ μ) (g, 1)) =
      ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
        (IntrinsicActiveClosure.CM.Intrinsic.assemble E L (τ μ) (g, 1)) :=
    SplittingProjection.CM.projection E L (τ μ) g 1
  have hc := ActiveProjection.CM.conjugation E L τ μ D.pel.reference hb c S hτ hr g
  exact hA.trans ((recover _ _ _ hc).trans
    (congrArg (fun a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => a⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
      (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic (CMExtraction.ActiveBlockMatrices.Local.activeBlockGL c μ (CMExtraction.Contragredient.Local.contragredient ℚ_[q] g))) * a) hSu.symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveWeilProjection.CM
