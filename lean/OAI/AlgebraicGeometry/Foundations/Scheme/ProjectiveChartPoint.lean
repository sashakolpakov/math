import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorScale
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChart

/-! # Projective Chart Point -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint

noncomputable section

/-!
# Actual affine chart points and normalized homogeneous coordinates

The inverse affine chart of the genuine projective scheme takes an evaluated
affine point to the vector point obtained by inserting a coordinate equal to one.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

/-- The scheme point obtained by evaluating the polynomial coordinates of a
standard affine chart and then including the chart in projective space. -/
def projectiveAffinePoint (n : ℕ) (i : Fin (n + 1))
    (a : {j : Fin (n + 1) // j ≠ i} → ℂ) : ProjectiveSpace.complexBase ⟶ ProjectiveSpace.projectiveSpace n :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)) ≫ ProjectiveChart.projectiveAffineChartMap n i

@[reassoc (attr := simp)]
theorem projectiveAffinePoint_over_base (n : ℕ) (i : Fin (n + 1))
    (a : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    projectiveAffinePoint n i a ≫ ProjectiveSpace.projectiveSpaceToBase n = 𝟙 ProjectiveSpace.complexBase := by
  rw [projectiveAffinePoint, Category.assoc, ProjectiveChart.projectiveAffineChartMap_over]
  have h : CommRingCat.ofHom (MvPolynomial.C : ℂ →+* ProjectiveChartToPolynomial.projectiveChartPolynomial n i) ≫
      CommRingCat.ofHom (MvPolynomial.eval a) = 𝟙 (CommRingCat.of ℂ) := by
    ext c
    simp
  rw [ProjectiveChart.projectiveChartPolynomialToBase, ← Spec.map_comp, h, Spec.map_id]

/-- Evaluation of the homogeneous fraction used to test a projective basic open. -/
theorem projectiveChartToPolynomial_isLocalizationElem (n : ℕ) (i : Fin (n + 1))
    (f : ProjectiveSpace.homogeneousCoordinateRing n) (d : ℕ) (hf : f ∈ ProjectiveSpace.projectiveGrading n d) :
    ProjectiveChartToPolynomial.projectiveChartToPolynomial n i
      (HomogeneousLocalization.Away.isLocalizationElem
        (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) hf) = DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i f := by
  simp only [HomogeneousLocalization.Away.isLocalizationElem,
    ProjectiveChartToPolynomial.projectiveChartToPolynomial_mk, pow_one]

/-- Projective basic opens pull back under an affine chart point according to
ordinary evaluation on the normalized homogeneous coordinate vector. -/
theorem projectiveAffinePoint_preimage_basicOpen (n : ℕ) (i : Fin (n + 1))
    (a : {j : Fin (n + 1) // j ≠ i} → ℂ)
    (f : ProjectiveSpace.homogeneousCoordinateRing n) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ ProjectiveSpace.projectiveGrading n d) :
    projectiveAffinePoint n i a ⁻¹ᵁ Proj.basicOpen (ProjectiveSpace.projectiveGrading n) f =
      PrimeSpectrum.basicOpen (MvPolynomial.eval (DehomogenizationC.Algebraic.Dehomogenization.insertOne i a) f) := by
  rw [projectiveAffinePoint, ProjectiveChart.projectiveAffineChartMap, ProjectiveChart.projectiveCoordinateIsoSpec_inv_ι]
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (𝒜 := ProjectiveSpace.projectiveGrading n)
      (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by decide : 0 < 1) hf hd,
    SpecMap_preimage_basicOpen, SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen
    (MvPolynomial.eval a (ProjectiveChartToPolynomial.projectiveChartToPolynomial n i
      (HomogeneousLocalization.Away.isLocalizationElem
        (ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) hf))) = _
  rw [projectiveChartToPolynomial_isLocalizationElem n i f d hf, DehomogenizationC.Algebraic.Dehomogenization.eval_dehomogenize]

/-- Homogeneous equations of an evaluated affine chart point, in every degree. -/
theorem projectiveAffinePoint_homogeneous_mem_iff (n : ℕ) (i : Fin (n + 1))
    (a : {j : Fin (n + 1) // j ≠ i} → ℂ)
    (f : ProjectiveSpace.homogeneousCoordinateRing n) (d : ℕ) (hf : f ∈ ProjectiveSpace.projectiveGrading n d)
    (x : ProjectiveSpace.complexBase) :
    f ∈ (projectiveAffinePoint n i a x).asHomogeneousIdeal ↔
      MvPolynomial.eval (DehomogenizationC.Algebraic.Dehomogenization.insertOne i a) f = 0 := by
  cases d with
  | zero =>
      obtain ⟨c, rfl⟩ : ∃ c : ℂ, f = MvPolynomial.C c :=
        ⟨_, HomogeneousEvalMap.eq_C_of_isHomogeneous_zero hf⟩
      simp only [MvPolynomial.eval_C]
      constructor
      · intro h
        by_contra hc
        let : (projectiveAffinePoint n i a x).asHomogeneousIdeal.toIdeal.IsPrime :=
          (projectiveAffinePoint n i a x).isPrime
        exact Ideal.notMem_of_isUnit
          (projectiveAffinePoint n i a x).asHomogeneousIdeal.toIdeal
          ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C) h
      · intro hc
        simp [hc]
  | succ d =>
      have h : projectiveAffinePoint n i a x ∈ Proj.basicOpen (ProjectiveSpace.projectiveGrading n) f ↔
          MvPolynomial.eval (DehomogenizationC.Algebraic.Dehomogenization.insertOne i a) f ≠ 0 := by
        change x ∈ projectiveAffinePoint n i a ⁻¹ᵁ Proj.basicOpen (ProjectiveSpace.projectiveGrading n) f ↔ _
        rw [projectiveAffinePoint_preimage_basicOpen n i a f (d + 1) (Nat.succ_pos d) hf]
        rw [Subsingleton.elim x (default : ProjectiveSpace.complexBase)]
        change MvPolynomial.eval (DehomogenizationC.Algebraic.Dehomogenization.insertOne i a) f ∉ (default : ProjectiveSpace.complexBase).asIdeal ↔ _
        rw [Scheme.default_asIdeal]
        rfl
      change (¬ f ∈ (projectiveAffinePoint n i a x).asHomogeneousIdeal ↔
        ¬ MvPolynomial.eval (DehomogenizationC.Algebraic.Dehomogenization.insertOne i a) f = 0) at h
      exact not_iff_not.mp h

/-- The normalized homogeneous vector associated to affine coordinates is nonzero. -/
theorem insertOne_ne_zero (n : ℕ) (i : Fin (n + 1))
    (a : {j : Fin (n + 1) // j ≠ i} → ℂ) : DehomogenizationC.Algebraic.Dehomogenization.insertOne i a ≠ 0 := by
  intro h
  have : (1 : ℂ) = 0 := by simpa using congrFun h i
  exact one_ne_zero this

/-- The actual inverse affine-chart morphism agrees with the vector-point
construction on normalized coordinates. -/
theorem projectiveAffineChartMap_eval_eq_vectorPoint (n : ℕ) (i : Fin (n + 1))
    (a : {j : Fin (n + 1) // j ≠ i} → ℂ) (hv : DehomogenizationC.Algebraic.Dehomogenization.insertOne i a ≠ 0) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)) ≫ ProjectiveChart.projectiveAffineChartMap n i =
      ProjectiveVectorPoint.projectiveVectorPoint (DehomogenizationC.Algebraic.Dehomogenization.insertOne i a) hv := by
  change projectiveAffinePoint n i a = _
  apply ext_of_apply_closedPoint_eq (ProjectiveSpace.projectiveSpaceToBase n)
    (projectiveAffinePoint_over_base n i a) (ProjectiveVectorPoint.projectiveVectorPoint_over_base (DehomogenizationC.Algebraic.Dehomogenization.insertOne i a) hv)
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d f hf
  exact (projectiveAffinePoint_homogeneous_mem_iff n i a f d hf
    (IsLocalRing.closedPoint ℂ)).trans
      (ProjectiveVectorScale.projectiveVectorPoint_homogeneous_mem_iff (DehomogenizationC.Algebraic.Dehomogenization.insertOne i a) hv f d hf
        (IsLocalRing.closedPoint ℂ)).symm

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint
