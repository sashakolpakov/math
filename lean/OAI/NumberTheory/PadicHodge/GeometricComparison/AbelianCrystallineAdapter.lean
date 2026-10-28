import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineOperators

/-! # Abelian Crystalline Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The crystalline adapter on GeometricComparison's actual abelian special fiber and extending endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.smallCrystallineEquiv : A.SmallCrystalline
    ≃ₛₗ[(GeometricComparison.Crystalline.CoefficientAdapter.coefficientFieldEquiv q).toRingHom] A.Crystalline := by
  have : IsProper A.specialFiber.scheme.hom := A.specialFiber.proper
  exact SmallCrystallineOperators.CrystallineAdapter.smallToBigEquiv q A.specialFiber.scheme

def Geometry.AbelianH1Model.smallCrystallinePullback (f : A.ExtendingEndomorphism) :
    Module.End (FractionRing (GeometricComparison.Crystalline.CoefficientAdapter.Witt q)) A.SmallCrystalline := by
  have : IsProper A.specialFiber.scheme.hom := A.specialFiber.proper
  exact SmallCrystallineOperators.CrystallineAdapter.smallPullback q (A.specialEndomorphism f)

def Geometry.AbelianH1Model.smallCrystallineFrobenius :
    Module.End (FractionRing (GeometricComparison.Crystalline.CoefficientAdapter.Witt q)) A.SmallCrystalline := by
  have : IsProper A.specialFiber.scheme.hom := A.specialFiber.proper
  exact SmallCrystallineOperators.CrystallineAdapter.smallFrobenius q A.specialFiber.scheme

theorem Geometry.AbelianH1Model.smallCrystallineEquiv_pullback (f : A.ExtendingEndomorphism) (x : A.SmallCrystalline) :
    A.smallCrystallineEquiv (A.smallCrystallinePullback f x) =
      A.crystallinePullback f (A.smallCrystallineEquiv x) := by
  have : IsProper A.specialFiber.scheme.hom := A.specialFiber.proper
  exact SmallCrystallineOperators.CrystallineAdapter.smallToBigEquiv_pullback q (A.specialEndomorphism f) x

theorem Geometry.AbelianH1Model.smallCrystallineEquiv_frobenius (x : A.SmallCrystalline) :
    A.smallCrystallineEquiv (A.smallCrystallineFrobenius x) =
      A.crystallineFrobenius (A.smallCrystallineEquiv x) := by
  have : IsProper A.specialFiber.scheme.hom := A.specialFiber.proper
  exact SmallCrystallineOperators.CrystallineAdapter.smallToBigEquiv_frobenius q A.specialFiber.scheme x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
