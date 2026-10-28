import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Albanese
import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # Albanese Cohomology -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseCohomology

noncomputable section

/-!
The supplied HodgeComparison comparison is used as a named hypothesis with its original
identity-section convention. The bridge to Construction's group-point identity `1`
is proved explicitly below.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

/-- HodgeComparison's original pointed universal property, retaining its `η` notation. -/
def IsAlbaneseMap (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) : Prop :=
  x₀ ≫ a = η[A.toOver] ∧
    ∀ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ B.toOver),
      x₀ ≫ f = η[B.toOver] → ∃! φ : A.toOver ⟶ B.toOver,
        IsMonHom φ ∧ a ≫ φ = f

/-- Construction and HodgeComparison use the same universal property. -/
theorem e08_isAlbanese_iff (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) :
    IsAlbaneseMap X x₀ A a ↔ Albanese.IsAlbaneseMap X.presentation x₀ A a := by
  simp only [IsAlbaneseMap, Albanese.IsAlbaneseMap, MonObj.one_eq_one]

/-- The canonical Betti Hodge pieces, exactly as in HodgeComparison. -/
def IsCanonicalH1 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1)) : Prop :=
  H.holomorphic =
      (V.pureBettiSubspace 1 0).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification
          (Betti.Scheme.schemePointSpace V.toOver) 1) ∧
  H.antiholomorphic =
      (V.pureBettiSubspace 0 1).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification
          (Betti.Scheme.schemePointSpace V.toOver) 1)

/-- The complete HodgeComparison comparison proposition, as an explicit input. -/
def HodgeComparisonInput : Prop :=
  ∀ (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
    IsAlbaneseMap X x₀ A a →
      ∃ (HA : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
        (HX : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
        (e : A.variety.rationalCohomology 1 ≃ₗ[ℚ] X.rationalCohomology 1),
        IsCanonicalH1 A.variety HA ∧
        IsCanonicalH1 X HX ∧
        e.toLinearMap = (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom ∧
        ComplexMultiplication.WeightOne.CM.IsHodgeMap HA HX e.toLinearMap ∧
        ComplexMultiplication.WeightOne.CM.IsHodgeMap HX HA e.symm.toLinearMap

/-- Construction and HodgeComparison give a characteristic-zero Albanese map that identifies
actual rational Betti H¹ and has a surjective finite difference-word map. -/
theorem exists_albanese_h1_and_finite_word
    (hConstruction : Albanese.ConstructionInput) (hHodgeComparison : HodgeComparisonInput)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) :
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver),
      Albanese.IsAlbaneseMap X.presentation x₀ A a ∧
      Function.Bijective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom ∧
      ∃ n : ℕ, 0 < n ∧ Surjective (Albanese.Construction.ImageWords.wordMap X.presentation A a n).left := by
  let : ConnectedSpace X.presentation.carrier :=
    inferInstanceAs (ConnectedSpace X.carrier)
  obtain ⟨A, a, ha, hn⟩ := Albanese.exists_albanese_with_finite_word hConstruction X.presentation x₀
  obtain ⟨_, _, e, _, _, he, _, _⟩ :=
    hHodgeComparison X x₀ A a ((e08_isAlbanese_iff X x₀ A a).mpr ha)
  refine ⟨A, a, ha, ?_, hn⟩
  rw [← he]
  exact e.bijective

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseCohomology
