import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartCoefficientSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CanonicalChartSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinateMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PolynomialChartPullback

/-! # Chart Point Function Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartPointFunctionValues

noncomputable section

/-! Pulling an actual affine-chart function to a spectrum evaluates
its chart-ring representative under the given ring homomorphism.
Normalized projective coordinates therefore evaluate homogeneous
polynomial chart fractions by their polynomial numerators. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem openSectionPullback_top {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    Open.SectionPullback.openSectionPullback f ⊤ ⊤ le_top r = f.appTop r := by
  change X.presheaf.map (𝟙 (.op (⊤ : X.Opens))) (f.appTop r) = _
  rw [X.presheaf.map_id]
  rfl

theorem affineChartPoint_functionValue
    {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}
    (U : X.Opens) (e : Spec (.of A) ≅ U.toScheme) (φ : A →+* B)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι) ⁻¹ᵁ U) (r : Γ(X, U)) :
    Open.SectionPullback.openSectionPullback (Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι) U ⊤ h r =
      (Scheme.ΓSpecIso (.of B)).inv (φ ((ChartCoefficientSections.affineChartSectionsIso U e).hom r)) := by
  let q := Spec.map (CommRingCat.ofHom φ) ≫ e.hom
  have hm : q ≫ U.ι = Spec.map (CommRingCat.ofHom φ) ≫ e.hom ≫ U.ι := Category.assoc _ _ _
  have hq : ⊤ ≤ (q ≫ U.ι) ⁻¹ᵁ U := by rw [hm]; exact h
  have hc := Open.SectionPullbackComposition.openSectionPullback_comp q U.ι U ⊤ ⊤ U.ι_preimage_self.ge le_top hq r
  simp only [hm] at hc
  rw [← hc, Open.SectionPullbackComposition.openSectionPullback_open_self, openSectionPullback_top]
  apply (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.injective
  change (Scheme.ΓSpecIso (.of B)).hom
      ((Spec.map (CommRingCat.ofHom φ)).appTop (e.hom.appTop (U.topIso.inv r))) =
    (Scheme.ΓSpecIso (.of B)).hom ((Scheme.ΓSpecIso (.of B)).inv
      (φ ((Scheme.ΓSpecIso (.of A)).hom (e.hom.appTop (U.topIso.inv r)))))
  rw [(Scheme.ΓSpecIso (.of B)).inv_hom_id_apply]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) _

theorem affineProjectiveCoordinateMap_polynomialValue
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n d : ℕ}
    (v : Fin (n + 1) → B) (i : Fin (n + 1)) (hi : v i = 1)
    (h : ⊤ ≤ AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) B v i hi ⁻¹ᵁ
      Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) :
    Open.SectionPullback.openSectionPullback (AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) B v i hi)
      (Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)) ⊤ h (Homogeneous.PolynomialChartPullback.homogeneousPolynomialChartFunction p i) =
      (Scheme.ΓSpecIso (.of B)).inv (MvPolynomial.eval₂Hom (algebraMap R B) v p.val) := by
  let U := Proj.basicOpen (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)
  let e := (Proj.basicOpenIsoSpec (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one).symm
  have he := affineChartPoint_functionValue U e
    (ProjectiveChart.Evaluation.projectiveChartEvaluation (algebraMap R B) v i hi) h (Homogeneous.PolynomialChartPullback.homogeneousPolynomialChartFunction p i)
  simp only [Homogeneous.PolynomialChartPullback.homogeneousPolynomialChartFunction] at he
  rw [Projective.CanonicalChartSections.projectiveAffineChartSectionsIso_awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one] at he
  have hev : ProjectiveChart.Evaluation.projectiveChartEvaluation (algebraMap R B) v i hi
      (HomogeneousLocalization.Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R i) p.property) =
        MvPolynomial.eval₂Hom (algebraMap R B) v p.val := by
    simpa only [HomogeneousLocalization.Away.isLocalizationElem, pow_one] using
      ProjectiveChart.Evaluation.projectiveChartEvaluation_mk (algebraMap R B) v i hi d p.val p.property
  rw [hev] at he
  exact he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartPointFunctionValues
