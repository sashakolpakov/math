import OAI.AlgebraicGeometry.Cycles.Functoriality.FundamentalDegreeTransport
import OAI.AlgebraicGeometry.Cycles.Functoriality.ImageOpen

/-! # Intrinsic Compact Degree -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.IntrinsicCompactDegree.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

instance openSchemePoints_t2Space (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (U : X.left.Opens) : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AnalyticRestriction.Construction.openSchemeOver X U)) :=
  (AnalyticRestriction.Construction.openSchemePointHomeomorph X U).isEmbedding.t2Space

instance openSchemePoints_secondCountableTopology (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (U : X.left.Opens) :
    SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AnalyticRestriction.Construction.openSchemeOver X U)) :=
  (AnalyticRestriction.Construction.openSchemePointHomeomorph X U).isEmbedding.secondCountableTopology

/-- For the actual complex points of a proper finite etale map of smooth
integral schemes, compact fundamental pushforward has its algebraic generic degree. -/
theorem nativeFiniteEtale_compactFundamental_degree
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [IsIntegral Y.left]
    [Smooth X.hom] [Smooth Y.hom]
    [T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
    (hf : IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f))
    (hη : f.left (genericPoint X.left) = genericPoint Y.left)
    (K : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (hK : IsCompact K) (n : ℕ)
    (hX : 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom = n)
    (hY : 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom = n) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
        (A := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n
      (FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' K) (hf.isCompact_preimage hK) n hX) =
    (f.left.residueDegree (genericPoint X.left) : ℚ) •
      FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
        K hK n hY := by
  apply FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree_map_degree
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) hf (IntrinsicEtale.Construction.isLocalDiffeomorph_nativeScheme_affineEtale f)
    (f.left.residueDegree (genericPoint X.left)) _ K hK n hX hY
  intro y
  exact IntrinsicFiberDegree.Construction.native_fiber_card_eq_residueDegree f hη y

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.IntrinsicCompactDegree.Construction
