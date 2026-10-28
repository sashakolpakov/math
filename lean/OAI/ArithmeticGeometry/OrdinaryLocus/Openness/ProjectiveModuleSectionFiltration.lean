import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistPresentationRange
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistColumnRange
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistLocalGenerators
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.HomogeneousGeneratorImage
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective

/-! # Projective Module Section Filtration -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveModuleSectionFiltration.Construction

noncomputable section

/-! The normalized image of a coherent projective module is eventually its weighted generator filtration. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory _root_.MvPolynomial

universe u

local instance projectiveModuleSectionFiltrationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance projectiveModuleSectionFiltrationBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveChartWeightedModulePiece (hfield : IsField Γ(Spec (.of R), ⊤))
    (N : (Proj (homogeneousSubmodule σ R)).Modules) (j : σ) {r : ℕ}
    (w : Fin r → Γ(N, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)) (d : Fin r → ℕ) (n : ℕ) :
    Submodule Γ(Spec (.of R), ⊤) ((BaseOpenSections.Construction.baseOpenSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)).obj N) := by
  letI := hfield.toField
  letI := BaseOpenSections.Construction.baseOpenSectionsAlgebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  letI := BaseOpenModuleTower.Construction.baseOpenModuleOverSections AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ N (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  letI := BaseOpenModuleTower.Construction.baseOpenModuleScalarTower AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ N (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  exact HomogeneousGeneratorImage.Construction.weightedPolynomialModulePiece
    (fun i => ProjectiveChartScalars.Construction.projectiveChartPolynomialAlgHom (R := R) j (MvPolynomial.X i))
    (show Fin r → (BaseOpenSections.Construction.baseOpenSectionsFunctor AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)).obj N from w) d n

theorem negativeTwist_presentation_normalized_weighted_range
    (hfield : IsField Γ(Spec (.of R), ⊤))
    {N : (Proj (homogeneousSubmodule σ R)).Modules} (j : σ) {r : ℕ} (d : Fin r → ℕ)
    (q : (∐ fun i => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)) ⟶ N)
    (n : ℕ) (hd : ∀ i, d i ≤ n)
    (hq : Function.Surjective
      (((AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.map q).app ⊤)) :
    (BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ N
      (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)).range =
    projectiveChartWeightedModulePiece hfield N j (NegativeTwistLocalGenerators.Construction.negativeTwistPresentationLocalGenerators j d q) d n := by
  let := hfield.toField
  let := BaseOpenSections.Construction.baseOpenSectionsAlgebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  let := BaseOpenModuleTower.Construction.baseOpenModuleOverSections AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ N (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  let := BaseOpenModuleTower.Construction.baseOpenModuleScalarTower AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ N (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  have h := NegativeTwistPresentationRange.Construction.negativeTwist_presentation_normalized_range j d q n hd hq
  refine h.trans ?_
  apply iSup_congr
  intro i
  exact NegativeTwistColumnRange.Construction.negativeTwistPolynomialColumn_normalized_range hfield j (d i) n (hd i)
    (Sigma.ι (fun k : Fin r =>
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)) i ≫ q)

theorem projective_module_normalized_image_eventually_weighted [IsNoetherianRing R]
    (hfield : IsField Γ(Spec (.of R), ⊤))
    (N : (Proj (homogeneousSubmodule σ R)).Modules) [N.IsQuasicoherent] [N.IsFiniteType] (j : σ) :
    ∃ (r : ℕ) (w : Fin r → Γ(N, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)) (d : Fin r → ℕ) (b : ℕ),
      Submodule.span Γ(Proj (homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) (Set.range w) = ⊤ ∧
      ∀ n : ℕ, b ≤ n →
        (BaseOpenSections.Construction.tensorSectionGlobalCoefficientLinear AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ N
          (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)).range =
        projectiveChartWeightedModulePiece hfield N j w d n := by
  classical
  obtain ⟨r, d, q, hq⟩ := AlgebraicGeometry.SheafCohomology.Projective.FixedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient N j
  have : Epi q := hq
  let M := ∐ fun i : Fin r => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)
  have : M.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent j d
  have : M.IsFiniteType := AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType j d
  obtain ⟨b, hb⟩ := AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective.MvPolynomial.finiteType_epi_eventually_projectiveTwist_sections_surjective (M := M) q j
  let B := max b (Finset.univ.sup d)
  refine ⟨r, NegativeTwistLocalGenerators.Construction.negativeTwistPresentationLocalGenerators j d q, d, B,
    NegativeTwistLocalGenerators.Construction.negativeTwistPresentationLocalGenerators_span j d q, fun n hn => ?_⟩
  have hd (i : Fin r) : d i ≤ n :=
    (Finset.le_sup (f := d) (Finset.mem_univ i)).trans ((le_max_right _ _).trans hn)
  exact negativeTwist_presentation_normalized_weighted_range hfield j d q n hd
    (hb n ((le_max_left _ _).trans hn))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveModuleSectionFiltration.Construction
