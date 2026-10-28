import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexPresentationAugmentation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationQuotientCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedMinimalCoverDegree

/-! # Complex Presentation Augmentation Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexPresentationAugmentationSections

noncomputable section

section

/-! The original sheaf augmentation agrees with the minimal graded cover on twisted sections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MvPolynomial
namespace ComplexResolution
variable {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra ComplexMinimalResolution.ComplexResolution.complexResolutionField
variable {j : σ} {M : (Proj (homogeneousSubmodule σ ℂ)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M)

theorem presentationLift_sections (n : ℕ)
    (hr : ∀ i, D.rowDegree i ≤ n)
    (hm : ∀ i, GradedMinimalFiniteCover.augmentationFinWeight D.gradedCokernel i ≤ n)
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := ℂ) j n).functor.obj
        (ComplexMinimalResolution.ComplexResolution.freeSheaf j D.gradedCokernel))) :
    ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := ℂ) j D.rowDegree n hr).hom
      ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := ℂ) j n).functor.map
          (ComplexPresentationAugmentation.ComplexResolution.presentationLift D)) x)).val =
      ComplexPresentationAugmentation.ComplexResolution.presentationLiftPolynomial D
        ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := ℂ) j
          (GradedMinimalFiniteCover.augmentationFinWeight D.gradedCokernel) n hm).hom x).val := by
  dsimp only [ComplexMinimalResolution.ComplexResolution.freeSheaf] at x
  unfold ComplexPresentationAugmentation.ComplexResolution.presentationLift
  convert GradedPolynomialMapSections.MvPolynomial.coordinateGradedPolynomialSheafMap_sections (R := ℂ) j D.rowDegree
    (GradedMinimalFiniteCover.augmentationFinWeight D.gradedCokernel) (ComplexPresentationAugmentation.ComplexResolution.presentationLiftPolynomial D)
    (ComplexPresentationAugmentation.ComplexResolution.presentationLiftPolynomial_homogeneous D) n hr hm x using 1

theorem presentationAugmentation_sections (n : ℕ)
    (hr : ∀ i, D.rowDegree i ≤ n)
    (hm : ∀ i, GradedMinimalFiniteCover.augmentationFinWeight D.gradedCokernel i ≤ n)
    (e : D.gradedCokernel.grading (n : ℤ) ≃ₗ[Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)]
      (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := σ))).obj
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := ℂ) j n).functor.obj M))
    (he : ∀ x, e (D.gradedCokernelProjectionDegree n
        ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := ℂ) j D.rowDegree n hr).hom x)) =
      (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := ℂ) j n).functor.map
          D.projection) x)
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := ℂ) j n).functor.obj
        (ComplexMinimalResolution.ComplexResolution.freeSheaf j D.gradedCokernel))) :
    e (GradedMinimalCoverDegree.augmentationFinProjectionDegree D.gradedCokernel D.gradedCokernel_nonnegative (n : ℤ)
      ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := ℂ) j
        (GradedMinimalFiniteCover.augmentationFinWeight D.gradedCokernel) n hm).hom x)) =
      (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := σ))).map
        ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := ℂ) j n).functor.map
          (ComplexPresentationAugmentation.ComplexResolution.presentationAugmentation D)) x := by
  dsimp only [ComplexMinimalResolution.ComplexResolution.freeSheaf] at x
  let G := AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := σ))
  let F := (PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := ℂ) j n).functor
  let y := G.map (F.map (ComplexPresentationAugmentation.ComplexResolution.presentationLift D)) x
  have hl := presentationLift_sections D n hr hm x
  change e _ = G.map (F.map (ComplexPresentationAugmentation.ComplexResolution.presentationLift D ≫ D.projection)) x
  rw [F.map_comp, G.map_comp, ModuleCat.comp_apply]
  change e _ = G.map (F.map D.projection) y
  rw [← he y]
  congr 1
  apply Subtype.ext
  change GradedMinimalFiniteCover.augmentationFinProjection D.gradedCokernel
      ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := ℂ) j
        (GradedMinimalFiniteCover.augmentationFinWeight D.gradedCokernel) n hm).hom x).val =
    D.polynomialMap.range.mkQ
      ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := ℂ) j D.rowDegree n hr).hom y).val
  dsimp only [y, F, G]
  have hq := congrArg D.polynomialMap.range.mkQ hl
  have hp := LinearMap.congr_fun (ComplexPresentationAugmentation.ComplexResolution.presentationLiftPolynomial_projection D)
    ((TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := ℂ) j
      (GradedMinimalFiniteCover.augmentationFinWeight D.gradedCokernel) n hm).hom x).val
  dsimp only [LinearMap.comp_apply] at hp
  refine hp.symm.trans ?_
  convert hq.symm using 1

end ComplexResolution

end

/-! The minimal sheaf resolution presents the original sheaf on all sufficiently large twists. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MvPolynomial
namespace ComplexResolution
variable {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra ComplexMinimalResolution.ComplexResolution.complexResolutionField
variable {j : σ} {M : (Proj (homogeneousSubmodule σ ℂ)).Modules}
    (D : TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M)

theorem presentationAugmentation_eventually_sections [M.IsQuasicoherent] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Function.Exact
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := σ))).map
          ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := ℂ) j n).functor.map
            (ComplexMinimalResolution.ComplexResolution.differential j D.gradedCokernel D.gradedCokernel_nonnegative 0))).hom
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := σ))).map
          ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := ℂ) j n).functor.map
            (ComplexPresentationAugmentation.ComplexResolution.presentationAugmentation D))).hom ∧
      Function.Surjective
        ((AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) (σ := σ))).map
          ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := ℂ) j n).functor.map
            (ComplexPresentationAugmentation.ComplexResolution.presentationAugmentation D))).hom := by
  obtain ⟨b, hb⟩ := D.eventually_gradedCokernel_sections_compatible
  let Q := D.gradedCokernel
  let w := GradedMinimalFiniteCover.augmentationFinWeight Q
  let v := GradedMinimalFiniteCover.augmentationFinWeight (GradedMinimalSyzygy.minimalGradedSyzygy Q)
  refine ⟨b + Finset.univ.sup w + Finset.univ.sup v, fun n hn => ?_⟩
  have hn' : b ≤ n := by omega
  obtain ⟨hr, e, he⟩ := hb n hn'
  have hw (i : Fin (GradedMinimalFiniteCover.augmentationRank Q)) : w i ≤ n := by
    have := Finset.le_sup (f := w) (Finset.mem_univ i)
    omega
  have hv (i : Fin (GradedMinimalFiniteCover.augmentationRank (GradedMinimalSyzygy.minimalGradedSyzygy Q))) : v i ≤ n := by
    have := Finset.le_sup (f := v) (Finset.mem_univ i)
    omega
  let E := (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := ℂ) j w n hw).toLinearEquiv
  let V := (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistCoproductPolynomialSectionsIso (R := ℂ) j v n hv).toLinearEquiv
  have ha := presentationAugmentation_sections D n hr hw e he
  constructor
  · apply ExactLinearCoordinates.exact_of_linearEquiv_coordinates V E e.symm _ _
      (GradedMinimalCoverDegree.minimalGradedResolutionStepDegree Q D.gradedCokernel_nonnegative (n : ℤ))
      (GradedMinimalCoverDegree.augmentationFinProjectionDegree Q D.gradedCokernel_nonnegative (n : ℤ))
    · intro x
      apply Subtype.ext
      rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply]
      convert GradedPolynomialMapSections.MvPolynomial.coordinateGradedPolynomialSheafMap_sections (R := ℂ) j w v
        (GradedMinimalResolutionStep.minimalGradedResolutionStep Q)
        (GradedMinimalResolutionStep.minimalGradedResolutionStep_homogeneous Q D.gradedCokernel_nonnegative) n hw hv x using 1
      dsimp +instances only [Q, w, v, ComplexMinimalResolution.ComplexResolution.differential, ComplexMinimalResolution.ComplexResolution.term, ComplexMinimalResolution.ComplexResolution.freeSheaf,
        GradedMinimalCoverDegree.minimalGradedResolutionStepDegree, HilbertScheme.Presentations.Graded.Exactness.GradedModules.degreeMap, LinearMap.codRestrict_apply,
        LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply]
      rfl
    · intro x
      dsimp only [w, Q] at x
      apply e.injective
      rw [e.apply_symm_apply]
      convert (ha x).symm using 1
      dsimp +instances only [E, Q, w, Iso.toLinearEquiv_apply, ComplexMinimalResolution.ComplexResolution.term, ComplexMinimalResolution.ComplexResolution.freeSheaf]
      rw [Iso.toLinearEquiv_apply]
    · exact GradedMinimalCoverDegree.minimalGradedResolutionStepDegree_exact Q D.gradedCokernel_nonnegative (n : ℤ)
  · intro y
    obtain ⟨z, hz⟩ := GradedMinimalCoverDegree.augmentationFinProjectionDegree_surjective Q D.gradedCokernel_nonnegative
      (n : ℤ) (e.symm y)
    obtain ⟨x, hx⟩ := E.surjective z
    dsimp only [w, Q] at x
    refine ⟨x, ?_⟩
    rw [← ha x]
    dsimp only [E, w, Q] at hx
    rw [Iso.toLinearEquiv_apply] at hx
    rw [hx, hz, e.apply_symm_apply]

end ComplexResolution

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexPresentationAugmentationSections
