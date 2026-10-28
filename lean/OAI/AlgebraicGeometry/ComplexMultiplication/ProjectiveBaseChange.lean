import OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartSchemeNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartBaseChange

/-! # Projective Base Change -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveBaseChange.ProjectiveCharts

noncomputable section

/-! # Base change of the actual polynomial projective schemes

The standard coordinate charts are categorical pullbacks. Their genuine finite
open cover assembles them into the global pullback square.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R S : Type) [CommRing R] [CommRing S]

theorem projectiveAffineChartMap_opensRange (n : ℕ) (i : Fin (n + 1)) :
    (ProjectiveChartSchemes.ProjectiveCharts.projectiveAffineChartMap R n i).opensRange = ProjectiveChartSchemes.ProjectiveCharts.projectiveCoordinateOpen R n i := by
  change ((ProjectiveChartSchemes.ProjectiveCharts.projectiveCoordinateIsoSpec R n i).inv ≫ (ProjectiveChartSchemes.ProjectiveCharts.projectiveCoordinateOpen R n i).ι).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact (ProjectiveChartSchemes.ProjectiveCharts.projectiveCoordinateOpen R n i).opensRange_ι

/-- The coefficient map restricts to precisely the original coordinate chart. -/
theorem projectiveCoordinateChart_isPullback (φ : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map φ :
        CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial R n i →+* CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial S n i)))
      (ProjectiveChartSchemes.ProjectiveCharts.projectiveAffineChartMap S n i) (ProjectiveChartSchemes.ProjectiveCharts.projectiveAffineChartMap R n i)
      (ProjectiveChartNaturality.ProjectiveCharts.projectiveCoefficientMap R S φ n) := by
  apply IsOpenImmersion.isPullback
  · exact ProjectiveChartSchemeNaturality.ProjectiveCharts.projectiveAffineChartMap_comp_projectiveCoefficientMap R S φ n i
  · rw [projectiveAffineChartMap_opensRange, projectiveAffineChartMap_opensRange]
    exact ProjectiveChartNaturality.ProjectiveCharts.projectiveCoefficientMap_preimage_coordinate R S φ n i

variable [Algebra R S]

/-- The genuine `Proj(S[X])` is the base change of the genuine `Proj(R[X])`. -/
theorem projectiveCoefficientMap_isPullback (n : ℕ) :
    IsPullback (ProjectiveChartNaturality.ProjectiveCharts.projectiveCoefficientMap R S (algebraMap R S) n)
      (ProjectiveChartSchemes.ProjectiveCharts.projectiveSpaceToBase S n) (ProjectiveChartSchemes.ProjectiveCharts.projectiveSpaceToBase R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (ProjectiveChartSchemes.ProjectiveCharts.projectivePolynomialOpenCover R n) ?_
  change ∀ i : Fin (n + 1), IsPullback
    (pullback.snd (ProjectiveChartNaturality.ProjectiveCharts.projectiveCoefficientMap R S (algebraMap R S) n)
      (ProjectiveChartSchemes.ProjectiveCharts.projectiveAffineChartMap R n i))
    (pullback.fst (ProjectiveChartNaturality.ProjectiveCharts.projectiveCoefficientMap R S (algebraMap R S) n)
        (ProjectiveChartSchemes.ProjectiveCharts.projectiveAffineChartMap R n i) ≫ ProjectiveChartSchemes.ProjectiveCharts.projectiveSpaceToBase S n)
    (ProjectiveChartSchemes.ProjectiveCharts.projectiveAffineChartMap R n i ≫ ProjectiveChartSchemes.ProjectiveCharts.projectiveSpaceToBase R n)
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  intro i
  let hi := projectiveCoordinateChart_isPullback R S (algebraMap R S) n i
  let e := hi.flip.isoPullback
  refine (ProjectiveChartBaseChange.ProjectiveCharts.projectivePolynomialChart_isPullback R S n i).of_iso e
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.refl_hom, Category.comp_id, e] using hi.flip.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom, Category.comp_id, e]
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    exact (ProjectiveChartSchemes.ProjectiveCharts.projectiveAffineChartMap_over S n i).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (ProjectiveChartSchemes.ProjectiveCharts.projectiveAffineChartMap_over R n i).symm
  · simp

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveBaseChange.ProjectiveCharts
