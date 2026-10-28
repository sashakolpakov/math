import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonModelMaps

/-! # Comparison Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM

noncomputable section

/-! A source map carried through the constructed comparison model.
The compatibility field is proved by canonical base-change naturality
in the constructor; it is not a hypothesis on a source theta family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}

structure SourceMap (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq) where
  integralSource : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q])
  genericSource : Over (NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K)
  integralMap : integralSource ⟶ A.integral.scheme
  genericMap : genericSource ⟶ A.variety.scheme
  sourceIso :
    (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).obj integralSource ≅
      (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).obj genericSource
  compatible :
    (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).map integralMap ≫ A.genericIso.hom =
      sourceIso.hom ≫ (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map genericMap

def sourceMap {S : Scheme} {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {X : Over S} (a : X ⟶ G.scheme)
    (k : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K ⟶ S) (t : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q] ⟶ S)
    (w : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) ≫ t = NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq ≫ k) :
    SourceMap (BaseChangeSquare.CM.ComparisonModel.model G k t w) where
  integralSource := (Over.pullback t).obj X
  genericSource := (Over.pullback k).obj X
  integralMap := (Over.pullback t).map a
  genericMap := (Over.pullback k).map a
  sourceIso := BaseChangeSquare.CM.squareIso (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])) (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) t k w X
  compatible := ComparisonModelMaps.CM.generic_map_compatible G a k t w

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComparisonModel.CM
