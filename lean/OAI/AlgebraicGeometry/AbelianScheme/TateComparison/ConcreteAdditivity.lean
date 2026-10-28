import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseProjectivity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiEndAdditivity
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalAlgebra

/-! # Concrete Additivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Additivity of the actual integral Betti pullback, using the constructed
projective presentation of the literal Albanese group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

include hg in
theorem Data.SphericalPELAlbaneseData.pullbackH1Integral_add (a b : D.EndK) :
    D.pullbackH1Integral (a + b) = D.pullbackH1Integral a + D.pullbackH1Integral b := by
  unfold Data.SphericalPELAlbaneseData.pullbackH1Integral
  rw [BaseChange.endSchemeMap_add, Functor.map_mul]
  apply LinearMap.ext
  exact HodgeConjecture.HeckeCycles.BettiEndAdditivity.CM.rational_pullback_mul (D.actualComplexAlbaneseVariety hg)
    ((Over.pullback D.complexGenericPoint).map (TateComparison.End.endSchemeMap D.albaneseGroup.X a))
    ((Over.pullback D.complexGenericPoint).map (TateComparison.End.endSchemeMap D.albaneseGroup.X b))

def Data.SphericalPELAlbaneseData.actualRationalH1Pullback : D.EndQ →ₗ[ℚ] Module.End ℚ D.H1 :=
  D.rationalH1Pullback (D.pullbackH1Integral_add hg)

theorem Data.SphericalPELAlbaneseData.actualRationalH1Pullback_spec (x : D.EndQ) :
    D.IsRationalH1Pullback x (D.actualRationalH1Pullback hg x) :=
  D.rationalH1Pullback_spec (D.pullbackH1Integral_add hg) x

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
