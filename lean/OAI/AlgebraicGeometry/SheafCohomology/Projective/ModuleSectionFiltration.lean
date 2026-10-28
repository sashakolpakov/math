import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistPresentationRange
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistColumnRange
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistLocalGenerators
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousGeneratorImage
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective

/-! # Module Section Filtration -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleSectionFiltration.Dimension

noncomputable section

/-! The normalized image of a coherent projective module is eventually its weighted generator filtration. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance projectiveModuleSectionFiltrationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X
local instance projectiveModuleSectionFiltrationBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveChartWeightedModulePiece (hfield : IsField Γ(Spec (.of R), ⊤))
    (N : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) {r : ℕ}
    (w : Fin r → Γ(N, MvPolynomialClosure.MvPolynomial.coordinateOpen j)) (d : Fin r → ℕ) (n : ℕ) :
    Submodule Γ(Spec (.of R), ⊤) ((ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsFunctor MvPolynomialClosure.MvPolynomial.homogeneousProjπ (MvPolynomialClosure.MvPolynomial.coordinateOpen j)).obj N) := by
  let := hfield.toField
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleOverSections MvPolynomialClosure.MvPolynomial.homogeneousProjπ N (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleScalarTower MvPolynomialClosure.MvPolynomial.homogeneousProjπ N (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  exact HomogeneousGeneratorImage.Dimension.weightedPolynomialModulePiece
    (fun i => ChartScalars.Dimension.projectiveChartPolynomialAlgHom (R := R) j (MvPolynomial.X i))
    (show Fin r → (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsFunctor MvPolynomialClosure.MvPolynomial.homogeneousProjπ (MvPolynomialClosure.MvPolynomial.coordinateOpen j)).obj N from w) d n

theorem negativeTwist_presentation_normalized_weighted_range
    (hfield : IsField Γ(Spec (.of R), ⊤))
    {N : (Proj (homogeneousSubmodule σ R)).Modules} (j : σ) {r : ℕ} (d : Fin r → ℕ)
    (q : (∐ fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)) ⟶ N)
    (n : ℕ) (hd : ∀ i, d i ≤ n)
    (hq : Function.Surjective
      (((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map q).app ⊤)) :
    (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear MvPolynomialClosure.MvPolynomial.homogeneousProjπ N
      (UnitSection.Dimension.projectiveTwistUnitSection j n) (MvPolynomialClosure.MvPolynomial.coordinateOpen j)).range =
    projectiveChartWeightedModulePiece hfield N j (NegativeTwistLocalGenerators.Dimension.negativeTwistPresentationLocalGenerators j d q) d n := by
  let := hfield.toField
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.baseOpenSectionsAlgebra (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleOverSections MvPolynomialClosure.MvPolynomial.homogeneousProjπ N (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  let := ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenModuleTower.Construction.baseOpenModuleScalarTower MvPolynomialClosure.MvPolynomial.homogeneousProjπ N (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  have h := NegativeTwistPresentationRange.Dimension.negativeTwist_presentation_normalized_range j d q n hd hq
  refine h.trans ?_
  apply iSup_congr
  intro i
  exact NegativeTwistColumnRange.Dimension.negativeTwistPolynomialColumn_normalized_range hfield j (d i) n (hd i)
    (Sigma.ι (fun k : Fin r =>
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)) i ≫ q)

theorem projective_module_normalized_image_eventually_weighted [IsNoetherianRing R]
    (hfield : IsField Γ(Spec (.of R), ⊤))
    (N : (Proj (homogeneousSubmodule σ R)).Modules) [N.IsQuasicoherent] [N.IsFiniteType] (j : σ) :
    ∃ (r : ℕ) (w : Fin r → Γ(N, MvPolynomialClosure.MvPolynomial.coordinateOpen j)) (d : Fin r → ℕ) (b : ℕ),
      Submodule.span Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen j) (Set.range w) = ⊤ ∧
      ∀ n : ℕ, b ≤ n →
        (ArithmeticGeometry.OrdinaryLocus.Openness.BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear MvPolynomialClosure.MvPolynomial.homogeneousProjπ N
          (UnitSection.Dimension.projectiveTwistUnitSection j n) (MvPolynomialClosure.MvPolynomial.coordinateOpen j)).range =
        projectiveChartWeightedModulePiece hfield N j w d n := by
  classical
  obtain ⟨r, d, q, hq⟩ := FixedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient N j
  have : Epi q := hq
  let M := ∐ fun i : Fin r => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)
  have : M.IsQuasicoherent := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent j d
  have : M.IsFiniteType := TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType j d
  obtain ⟨b, hb⟩ := GlobalSectionsSurjective.MvPolynomial.finiteType_epi_eventually_projectiveTwist_sections_surjective (M := M) q j
  let B := max b (Finset.univ.sup d)
  refine ⟨r, NegativeTwistLocalGenerators.Dimension.negativeTwistPresentationLocalGenerators j d q, d, B,
    NegativeTwistLocalGenerators.Dimension.negativeTwistPresentationLocalGenerators_span j d q, fun n hn => ?_⟩
  have hd (i : Fin r) : d i ≤ n :=
    (Finset.le_sup (f := d) (Finset.mem_univ i)).trans ((le_max_right _ _).trans hn)
  exact negativeTwist_presentation_normalized_weighted_range hfield j d q n hd
    (hb n ((le_max_left _ _).trans hn))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleSectionFiltration.Dimension
