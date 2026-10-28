import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety
import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # Definitions -/

namespace OAI.AlgebraicGeometry.Albanese.Definitions.CM.HodgeComparison

noncomputable section

/-! Definitions used in the HodgeComparison statement. -/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

/-- The pointed universal property of the Albanese variety. -/
def IsAlbaneseMap
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) : Prop :=
  x₀ ≫ a = η[A.toOver] ∧
  ∀ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ B.toOver),
    x₀ ≫ f = η[B.toOver] →
      ∃! g : A.toOver ⟶ B.toOver,
        IsMonHom g ∧ a ≫ g = f

/-- Anchor a weight-one structure to the actual geometric Hodge pieces. -/
def IsCanonicalH1
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1)) : Prop :=
  H.holomorphic =
      (V.pureBettiSubspace 1 0).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification
          (Betti.Scheme.schemePointSpace V.toOver) 1) ∧
  H.antiholomorphic =
      (V.pureBettiSubspace 0 1).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification
          (Betti.Scheme.schemePointSpace V.toOver) 1)

end

end OAI.AlgebraicGeometry.Albanese.Definitions.CM.HodgeComparison
