import OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartSchemes

/-! # Projective Chart Scheme Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartSchemeNaturality.ProjectiveCharts

noncomputable section

/-! # Genuine Proj coefficient change in affine coordinates -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R S : Type) [CommRing R] [CommRing S]

private theorem awayι_comp_map_of_eq (φ : R →+* S) (n : ℕ) (i : Fin (n + 1))
    (t : CMProjectiveCharts.ProjectiveCharts.homogeneousCoordinateRing S n) (ht : t ∈ CMProjectiveCharts.ProjectiveCharts.projectiveGrading S n 1)
    (hgt : ProjectiveChartNaturality.ProjectiveCharts.gradedCoefficientMap R S φ n (MvPolynomial.X i) = t) :
    Proj.awayι (CMProjectiveCharts.ProjectiveCharts.projectiveGrading S n) t ht (by decide : 0 < 1) ≫
      ProjectiveChartNaturality.ProjectiveCharts.projectiveCoefficientMap R S φ n =
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.map (ProjectiveChartNaturality.ProjectiveCharts.gradedCoefficientMap R S φ n)
            (P := Submonoid.powers (MvPolynomial.X i)) (Q := Submonoid.powers t) (by
              rintro _ ⟨k, rfl⟩
              exact ⟨k, by simp [hgt]⟩))) ≫
          Proj.awayι (CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n) (MvPolynomial.X i)
            (CMProjectiveCharts.ProjectiveCharts.projectiveVariable_homogeneous R n i) (by decide : 0 < 1) := by
  subst t
  exact Proj.awayι_comp_map (ProjectiveChartNaturality.ProjectiveCharts.gradedCoefficientMap R S φ n)
    (ProjectiveChartNaturality.ProjectiveCharts.irrelevant_le_map_gradedCoefficientMap R S φ n) (by decide : 0 < 1)
    (MvPolynomial.X i) (CMProjectiveCharts.ProjectiveCharts.projectiveVariable_homogeneous R n i)

/-- On a homogeneous chart, the actual Proj map is the actual homogeneous localization map. -/
theorem awayι_comp_projectiveCoefficientMap (φ : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    Proj.awayι (CMProjectiveCharts.ProjectiveCharts.projectiveGrading S n) (MvPolynomial.X i)
        (CMProjectiveCharts.ProjectiveCharts.projectiveVariable_homogeneous S n i) (by decide : 0 < 1) ≫
      ProjectiveChartNaturality.ProjectiveCharts.projectiveCoefficientMap R S φ n =
        Spec.map (CommRingCat.ofHom (ProjectiveChartNaturality.ProjectiveCharts.projectiveChartCoefficientMap R S φ n i)) ≫
          Proj.awayι (CMProjectiveCharts.ProjectiveCharts.projectiveGrading R n) (MvPolynomial.X i)
            (CMProjectiveCharts.ProjectiveCharts.projectiveVariable_homogeneous R n i) (by decide : 0 < 1) := by
  exact awayι_comp_map_of_eq R S φ n i (MvPolynomial.X i)
    (CMProjectiveCharts.ProjectiveCharts.projectiveVariable_homogeneous S n i) (ProjectiveChartNaturality.ProjectiveCharts.gradedCoefficientMap_X R S φ n i)

/-- In the proved affine coordinates, the genuine scheme map is polynomial coefficient change. -/
theorem projectiveAffineChartMap_comp_projectiveCoefficientMap (φ : R →+* S) (n : ℕ)
    (i : Fin (n + 1)) :
    ProjectiveChartSchemes.ProjectiveCharts.projectiveAffineChartMap S n i ≫ ProjectiveChartNaturality.ProjectiveCharts.projectiveCoefficientMap R S φ n =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.map φ : CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial R n i →+* CMProjectiveCharts.ProjectiveCharts.projectiveChartPolynomial S n i)) ≫
          ProjectiveChartSchemes.ProjectiveCharts.projectiveAffineChartMap R n i := by
  simp only [ProjectiveChartSchemes.ProjectiveCharts.projectiveAffineChartMap, ProjectiveChartSchemes.ProjectiveCharts.projectiveCoordinateIsoSpec_inv_ι]
  rw [Category.assoc, awayι_comp_projectiveCoefficientMap, ← Category.assoc,
    ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact ProjectiveChartNaturality.ProjectiveCharts.projectiveChartCoefficientMap_dehomogenizes R S φ n i c

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveChartSchemeNaturality.ProjectiveCharts
