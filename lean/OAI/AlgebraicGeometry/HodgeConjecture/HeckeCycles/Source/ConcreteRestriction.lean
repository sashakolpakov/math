import Lean.LibrarySuggestions.Basic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRestrictionExtraction

/-! # Concrete Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ConcreteRestriction.CM

noncomputable section

/-! Specialize the reference pullback to the actual source GeometricTheta data
before inserting the complete ordinary model. -/

open scoped Classical _root_.NumberField _root_.Manifold ContDiff TensorProduct
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K places.count q)
  (hb : D.reference.b = B.b) (hμ : D.reference.μ = E.val.toRingHom)
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice) (hN : 0 < D.level)
  (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice D.reference.lattice)

local notation "T" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM.data E L D hb b hN

include hμ in
theorem reference_extraction
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hc : (T).HasFiniteCoordinates)
    (W : Geometric.ThetaWitness.CM.Witness T hg hq hIsogenyQuotient)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (hφ : Theta.Weil.CM.finiteWeilInput φ ∈ (T).sphericalInputs)
    (Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : (CoverFactor.CM.withLattice E B D.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2).Domain → Y.analyticSpace)
    (hπ : (CoverFactor.CM.withLattice E B D.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover D.level Y π)
    (α : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms Y.analyticModel Y.analyticSpace 1 0)
    (hα : GeometricSource.CM.RepresentsTheta E L φ Y π α)
    (θY : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology 1))
    (hθY : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1 θY =
      (Y.deRhamBettiIso 1).hom (Y.deRhamClass 1 α.val))
    (hextract : Geometric.ThetaBettiClass.CM.classMap T hg hq hIsogenyQuotient W
      ⟨Theta.Weil.CM.finiteWeilInput φ, hφ⟩ ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v (CMExtraction.Intrinsic.Base.nativeH1 T hHodgeDecomposition hg)) :
    θY ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v
      (CMExtraction.Mem.canonicalH1 hHodgeDecomposition Y.presentation) := by
  exact SourceGeometric.ThetaRestrictionExtraction.CM.reference_extraction E L T rfl rfl hb hμ hΛ v
    hHodgeDecomposition hg hq hIsogenyQuotient hc W φ hφ Y π hπ α hα θY hθY hextract

--
--

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ConcreteRestriction.CM
