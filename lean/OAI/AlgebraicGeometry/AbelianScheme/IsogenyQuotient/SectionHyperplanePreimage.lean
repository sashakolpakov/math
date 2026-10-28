import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LinearHyperplaneAvoidance
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LinearSectionCombinations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages

/-! # Section Hyperplane Preimage -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionHyperplanePreimage.Construction

noncomputable section

/-! Pullback of an actual linear hyperplane under the morphism defined
by sections is the nonvanishing open of their linear combination. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages

universe u
variable {R : Type u} [CommRing R] {T S X : Scheme.{u}} {M : X.Modules} {n : ℕ}

theorem projectiveChartMap_preimage_linear (a : R →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1)
    (c : Fin (n + 1) → R) :
    AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartMap a v i hi ⁻¹ᵁ
      Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial c) =
        T.basicOpen (∑ j, a (c j) * v j) := by
  let z : AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing R n i := HomogeneousLocalization.Away.isLocalizationElem
    (MvPolynomial.isHomogeneous_X R i) (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial_homogeneous c)
  have hz : AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation a v i hi z = ∑ j, a (c j) * v j := by
    have he := AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation_mk a v i hi 1 (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial c)
      (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial_homogeneous c)
    simpa only [z, HomogeneousLocalization.Away.isLocalizationElem, pow_one] using
      he.trans (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial_eval a v c)
  have ha : Proj.awayι (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one ⁻¹ᵁ
      Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial c) =
      PrimeSpectrum.basicOpen z :=
    Proj.awayι_preimage_basicOpen (𝒜 := AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one
      (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial_homogeneous c) Nat.zero_lt_one
  have hp : Spec.map (CommRingCat.ofHom (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation a v i hi)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen z = PrimeSpectrum.basicOpen (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation a v i hi z) := by
    ext q
    rfl
  change T.toSpecΓ ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation a v i hi)) ⁻¹ᵁ
    (Proj.awayι (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one ⁻¹ᵁ
      Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial c))) = _
  rw [ha, hp, hz, Scheme.toSpecΓ_preimage_basicOpen]

theorem sectionAbsoluteChart_preimage_linear (f : X ⟶ S)
    (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)) (i : Fin (n + 1))
    (c : Fin (n + 1) → Γ(S, ⊤)) :
    AbelianModuli.HilbertConstruction.Section.ChartOverlaps.sectionAbsoluteChart f s i ⁻¹ᵁ
      Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial c) =
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).ι ⁻¹ᵁ
        AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (LinearSectionCombinations.Construction.sectionCombination s (fun j => f.appTop (c j))) := by
  let j := (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).ι
  let e := AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j (s i)
  have hc : AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate e
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j (LinearSectionCombinations.Construction.sectionCombination s (fun k => f.appTop (c k)))) =
      ∑ k, (j ≫ f).appTop (c k) * AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio (s i) (s k) := by
    rw [LinearSectionCombinations.Construction.pullbackSection_combination, LinearSectionCombinations.Construction.frameCoordinate_sectionCombination]
    apply Finset.sum_congr rfl
    intro k _
    rw [AbelianModuli.HilbertConstruction.Frame.Coordinates.sectionRatio_eq_frameCoordinate]
    rfl
  exact (projectiveChartMap_preimage_linear (j ≫ f).appTop.hom
    (fun k => AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio (s i) (s k)) i (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio_self (s i)) c).trans
      ((congrArg (fun a => (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).toScheme.basicOpen a) hc.symm).trans
        ((AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate e _).symm.trans
          (AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback j _)))

theorem sectionAbsoluteMorphism_preimage_linear (f : X ⟶ S)
    (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (c : Fin (n + 1) → Γ(S, ⊤)) :
    AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ⁻¹ᵁ
      Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial c) =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (LinearSectionCombinations.Construction.sectionCombination s (fun j => f.appTop (c j))) := by
  ext x
  obtain ⟨i, hi⟩ := hs x
  have he : (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).ι ⁻¹ᵁ (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ⁻¹ᵁ
      Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial c)) =
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).ι ⁻¹ᵁ
        AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (LinearSectionCombinations.Construction.sectionCombination s (fun j => f.appTop (c j))) :=
    (congrArg (fun a => a ⁻¹ᵁ
      Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (LinearHyperplaneAvoidance.Construction.sectionLinearPolynomial c))
      (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict f s hs i)).trans
        (sectionAbsoluteChart_preimage_linear f s i c)
  exact (congrArg (fun U => (⟨x, hi⟩ : (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i)).toScheme) ∈ U) he).to_iff

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionHyperplanePreimage.Construction
