import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PrincipalCoordinates

/-! # Theta Finite Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaFiniteCoordinates.CM

noncomputable section

/-! The actual GeometricTheta candidate satisfies the complete finite-coordinate
predicate: native local characters, standard lattices, and exact marked
away membership including every non-active q-adic block. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K places.count q) (hb : D.reference.b = B.b)
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice) (hN : 0 < D.level)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hstandard : ∀ v, CMExtraction.SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice v =
    RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q))

include hg hq hstandard in
theorem coordinates : (ThetaCandidate.CM.data E L D hb b hN).HasFiniteCoordinates := by
  refine ⟨CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers D, hstandard, ?_⟩
  intro g
  have hm := Rational.CoefficientTransport.CM.matrix D.reference.b B.b hb g
  have hs := (Source.MarkedAwayLevel.CM.rational_mem E L D.reference hb
    (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false)) b D.level hN
    (Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb g)).trans
    (Source.PrincipalCoordinates.CM.principal_iff E (OppositeCoordinates.CM.coordinates E L.coordinates)
      D hb hg hq hstandard b D.level hN hq.2.2.1
      (Rational.CoefficientTransport.CM.equivalence D.reference.b B.b hb g))
  have hlin := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 3) E =>
    (Matrix.SpecialLinearGroup.toLin' a).restrictScalars ℚ) hm
  have hlocal := congrArg (fun a : Matrix.SpecialLinearGroup (Fin 3) E =>
    ∀ v : Fin places.count × Bool, v.1 ≠ D.reference.distinguished →
      Matrix.SpecialLinearGroup.map (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) a ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) hm
  exact hs.trans (and_congr
    (Iff.of_eq (congrArg (fun a => a ∈ AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup
      (CMExtraction.LocalizedLatticeMaps.TestTransport.powerLocalizedLattice D.reference.lattice q).toAddSubgroup D.level) hlin))
    (Iff.of_eq hlocal))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaFiniteCoordinates.CM
