import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.Theta
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison

/-! # Theta Named -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaNamed.CM

noncomputable section

/-! Combine the entire named TateComparison and GeometricTheta inputs before specializing
their candidate to the concrete source representation. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]
  [Group MpR] [Group MpF] [Group MpA]

theorem apply (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (hTateComparison : TateComparison.CM.TateComparisonInput) (hGeometricTheta : Theta.CM.GeometricThetaInput)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (hcoordinates : D.HasFiniteCoordinates) (hholomorphic : D.HasHolomorphicThetaData)
    (hcovariance : D.HasRationalThetaCovariance) (hdense : DenseRange D.rationalFinite) :
    Theta.CM.Output D hg hq hIsogenyQuotient :=
  Theta.CM.from_input D hg hq hIsogenyQuotient hGeometricTheta hs hdegree
    (hTateComparison s hs hdegree q D.pel hg hq hIsogenyQuotient hConstruction hElementaryDivisors)
    hcoordinates hholomorphic hcovariance hdense

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaNamed.CM
