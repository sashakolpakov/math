import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel

/-! # Comparison Model Maps -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonModelMaps.CM

noncomputable section

/-! Naturality for an arbitrary map into the abelian scheme underlying
the comparison model, before instantiating the arithmetic Albanese data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.SpecialFiber

theorem generic_map_compatible
    {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]}
    {S : Scheme} {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    {X : Over S} (a : X ⟶ G.scheme)
    (k : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase K ⟶ S) (t : NumberTheory.PadicHodge.GeometricComparison.Geometry.ringBase ℤ_[q] ⟶ S)
    (w : NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]) ≫ t = NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq ≫ k) :
    (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).map ((Over.pullback t).map a) ≫
        (BaseChangeSquare.CM.ComparisonModel.genericIso G k t w).hom =
      (BaseChangeSquare.CM.squareIso (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q])) (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq) t k w X).hom ≫
        (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map ((Over.pullback k).map a) := by
  rw [BaseChangeSquare.CM.squareIso_comparisonModel]
  exact BaseChangeSquare.CM.squareIso_naturality _ _ _ _ w a

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonModelMaps.CM
