import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveWeilProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.AwayPhase

/-! # Theta Radial Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRadialCoordinates.CM

noncomputable section

/-! The actual original-source GeometricTheta datum satisfies both finite
coordinate identities used in the same-character radial argument. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.WeilData.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K places.count q) (hb : D.reference.b = B.b)
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice) (hN : 0 < D.level)
  {n : ℕ} (c : GeometricSource.CM.Positions E places ≃ Fin n) (u : Source.WeilData.CM.FiniteCoverGroup E places)
  (hu : FixedFrameAuxiliaryFamily.CM.Family.CoordinateIdentity E (ThetaCandidate.CM.data E L D hb b hN)
    (Source.ComplexAction.CM.Symplectic.frame E L.coordinates) u)

include c hu

theorem active (hq : D.IsGoodCompletelySplitPrime) (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    (ThetaCandidate.CM.data E L D hb b hN).weil.finite.project ((ThetaCandidate.CM.data E L D hb b hN).splitting (g, 1)) =
      ((ThetaCandidate.CM.data E L D hb b hN).weil.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (CMExtraction.ActiveBlockMatrices.Local.activeBlockGL c D.reference.distinguished (CMExtraction.Contragredient.Local.contragredient ℚ_[q] g))) *
            (ThetaCandidate.CM.data E L D hb b hN).weil.finite.project u :=
  Source.ActiveWeilProjection.CM.projection E L (ThetaCandidate.CM.data E L D hb b hN) hb rfl hq c u hu g

omit [IsGalois ℚ E] in
theorem away (w : Source.FactorTheta.CM.RationalWeilFactorization.Away E L
    (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))) (p t : Fin 3 → ℚ_[q]) :
    ((ThetaCandidate.CM.data E L D hb b hN).weil.finite.project
      (u * (ThetaCandidate.CM.data E L D hb b hN).splitting (1, w) * u⁻¹)).val *ᵥ
      Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.reference.distinguished p)
        (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.reference.distinguished t) =
      Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.reference.distinguished p)
        (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.reference.distinguished t) :=
  Source.AwayPhase.CM.fixes E L (ThetaCandidate.CM.data E L D hb b hN) hb rfl c u hu w p t

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRadialCoordinates.CM
