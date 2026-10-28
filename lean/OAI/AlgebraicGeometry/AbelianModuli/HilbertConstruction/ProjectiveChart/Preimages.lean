import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Preimages -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages

noncomputable section

/-! The constructed projective morphism pulls the standard charts back to the original nonvanishing opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {T S X : Scheme.{u}} {L : X.Modules} {n : ℕ}

/-- The preimage of the jth standard projective chart is the nonvanishing open of the jth coordinate. -/
theorem projectiveChartMap_preimage (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤))
    (i : Fin (n + 1)) (hi : v i = 1) (j : Fin (n + 1)) :
    Evaluation.projectiveChartMap c v i hi ⁻¹ᵁ Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X j) =
      T.basicOpen (v j) := by
  let z : Evaluation.projectiveChartRing R n i := HomogeneousLocalization.Away.isLocalizationElem
    (MvPolynomial.isHomogeneous_X R i) (MvPolynomial.isHomogeneous_X R j)
  have hz : Evaluation.projectiveChartEvaluation c v i hi z = v j := by
    simpa only [z, HomogeneousLocalization.Away.isLocalizationElem, pow_one] using
      Evaluation.projectiveChartEvaluation_coordinate c v i hi j
  have ha : Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one ⁻¹ᵁ
      Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X j) = PrimeSpectrum.basicOpen z :=
    Proj.awayι_preimage_basicOpen (𝒜 := Projective.ProjectivePresentations.coordinateGrading R n)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one
  have hp : Spec.map (CommRingCat.ofHom (Evaluation.projectiveChartEvaluation c v i hi)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen z = PrimeSpectrum.basicOpen (Evaluation.projectiveChartEvaluation c v i hi z) := by
    ext q
    rfl
  change T.toSpecΓ ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (Evaluation.projectiveChartEvaluation c v i hi)) ⁻¹ᵁ
    (Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one ⁻¹ᵁ
      Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X j))) = _
  rw [ha, hp, hz, Scheme.toSpecΓ_preimage_basicOpen]

/-- The jth chart pulls back under the ith section chart to the restriction of the jth section's
nonvanishing open. -/
theorem sectionAbsoluteChart_preimage (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L)) (i j : Fin (n + 1)) :
    Section.ChartOverlaps.sectionAbsoluteChart f s i ⁻¹ᵁ
      Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X j) =
      (Ample.LineBundles.sectionNonvanishing (s i)).ι ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing (s j) := by
  have hr := Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate
    (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (s i)).ι (s i))
    (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing (s i)).ι (s j))
  have hratio := Frame.Coordinates.sectionRatio_eq_frameCoordinate (s i) (s j)
  exact (projectiveChartMap_preimage ((Ample.LineBundles.sectionNonvanishing (s i)).ι ≫ f).appTop.hom
    (fun k => Section.Frames.sectionRatio (s i) (s k)) i (Section.Frames.sectionRatio_self (s i)) j).trans
      ((congrArg (fun a => (Ample.LineBundles.sectionNonvanishing (s i)).toScheme.basicOpen a) hratio).trans
        (hr.symm.trans (Section.Nonvanishing.sectionNonvanishing_pullback (Ample.LineBundles.sectionNonvanishing (s i)).ι (s j))))

/-- The global projective morphism has exactly the required standard-chart preimages. -/
theorem sectionAbsoluteMorphism_preimage (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) (j : Fin (n + 1)) :
    SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ⁻¹ᵁ
      Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X j) = Ample.LineBundles.sectionNonvanishing (s j) := by
  ext x
  obtain ⟨i, hi⟩ := hs x
  have he : (Ample.LineBundles.sectionNonvanishing (s i)).ι ⁻¹ᵁ (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ⁻¹ᵁ
      Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X j)) =
      (Ample.LineBundles.sectionNonvanishing (s i)).ι ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing (s j) :=
    (congrArg (fun a => a ⁻¹ᵁ Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X j))
      (SectionsProjectiveMorphism.sectionAbsoluteMorphism_restrict f s hs i)).trans (sectionAbsoluteChart_preimage f s i j)
  exact (congrArg (fun U => (⟨x, hi⟩ : (Ample.LineBundles.sectionNonvanishing (s i)).toScheme) ∈ U) he).to_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages
