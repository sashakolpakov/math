import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.OverlapMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality

/-! # Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.CoefficientNaturality

noncomputable section

/-! Normalized projective chart maps commute with changes of the coefficient
ring. This compares the actual homogeneous-localization evaluations. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] {n : ℕ}

theorem homogeneousFractionEvaluation_coefficientMap (φ : R →+* A) (c : A →+* B)
    (v : Fin (n + 1) → B) (f : Projective.ProjectivePresentations.coordinateRing R n) (d : ℕ)
    (hfd : f ∈ Projective.ProjectivePresentations.coordinateGrading R n d)
    (hf : IsUnit (MvPolynomial.eval₂Hom (c.comp φ) v f))
    (hg : IsUnit (MvPolynomial.eval₂Hom c v (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ f))) :
    (Homogeneous.Fractions.homogeneousFractionEvaluation c v (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ f) hg).comp
        (HomogeneousLocalization.Away.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ) f) =
      Homogeneous.Fractions.homogeneousFractionEvaluation (c.comp φ) v f hf := by
  let g := HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (n := n) φ
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hf
  have hga : MvPolynomial.eval₂Hom c v (g f) * a = 1 := by
    change MvPolynomial.eval₂Hom c v (MvPolynomial.map φ f) * a = 1
    rw [MvPolynomial.eval₂Hom_map_hom]
    exact ha
  apply RingHom.ext
  intro z
  obtain ⟨k, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (Projective.ProjectivePresentations.coordinateGrading R n) hfd z
  change Homogeneous.Fractions.homogeneousFractionEvaluation c v (g f) hg
      (HomogeneousLocalization.Away.map g f
        (HomogeneousLocalization.Away.mk (Projective.ProjectivePresentations.coordinateGrading R n) hfd k p hp)) = _
  rw [HomogeneousLocalization.Away.map_mk]
  exact (Homogeneous.Fractions.homogeneousFractionEvaluation_mk c v (g f) hg d (g.map_mem hfd)
    k (g p) (g.map_mem hp) a hga).trans
    ((congrArg (fun q => q * a ^ k) (MvPolynomial.eval₂Hom_map_hom φ v c p)).trans
      (Homogeneous.Fractions.homogeneousFractionEvaluation_mk (c.comp φ) v f hf d hfd k p hp a ha).symm)

variable {T : Scheme.{u}}

theorem projectiveFractionMap_coefficientMap (φ : R →+* A) (c : A →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (f : Projective.ProjectivePresentations.coordinateRing R n) (d : ℕ)
    (hfd : f ∈ Projective.ProjectivePresentations.coordinateGrading R n d) (hd : 0 < d)
    (hf : IsUnit (MvPolynomial.eval₂Hom (c.comp φ) v f))
    (hg : IsUnit (MvPolynomial.eval₂Hom c v (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ f))) :
    Chart.OverlapMaps.projectiveFractionMap c v (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ f) hg d
        ((HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ).map_mem hfd) hd ≫
          Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n =
      Chart.OverlapMaps.projectiveFractionMap (c.comp φ) v f hf d hfd hd := by
  let : Algebra R A := φ.toAlgebra
  let g := HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (n := n) φ
  have he := homogeneousFractionEvaluation_coefficientMap φ c v f d hfd hf hg
  change (T.toSpecΓ ≫ Spec.map
      (CommRingCat.ofHom (Homogeneous.Fractions.homogeneousFractionEvaluation c v (g f) hg)) ≫
      Proj.awayι (Projective.ProjectivePresentations.coordinateGrading A n) (g f) (g.map_mem hfd) hd) ≫ Proj.map g _ = _
  rw [Category.assoc, Category.assoc,
    Proj.awayι_comp_map g (Polynomial.ProjectiveCoefficients.polynomial_irrelevant_coefficient (R := R) (A := A)) hd f hfd,
    ← Spec.map_comp_assoc]
  change T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      ((Homogeneous.Fractions.homogeneousFractionEvaluation c v (g f) hg).comp
        (HomogeneousLocalization.Away.map g f))) ≫
      Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) f hfd hd = _
  rw [he]
  rfl

theorem projectiveChartMap_coefficientMap (φ : R →+* A) (c : A →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) :
    Evaluation.projectiveChartMap c v i hi ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n =
      Evaluation.projectiveChartMap (c.comp φ) v i hi := by
  let g := HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (n := n) φ
  have hR : IsUnit (MvPolynomial.eval₂Hom (c.comp φ) v (MvPolynomial.X i)) := by
    rw [MvPolynomial.eval₂Hom_X', hi]
    exact isUnit_one
  have hA : IsUnit (MvPolynomial.eval₂Hom c v (MvPolynomial.X i)) := by
    rw [MvPolynomial.eval₂Hom_X', hi]
    exact isUnit_one
  let P (z : Projective.ProjectivePresentations.coordinateGrading A n 1) : Prop := ∀ hz,
    Chart.OverlapMaps.projectiveFractionMap c v z.val hz 1 z.property Nat.zero_lt_one ≫
        Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n =
      Chart.OverlapMaps.projectiveFractionMap (c.comp φ) v (MvPolynomial.X i) hR 1
        (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one
  have hP : P ⟨g (MvPolynomial.X i), g.map_mem (MvPolynomial.isHomogeneous_X R i)⟩ := by
    intro hz
    exact projectiveFractionMap_coefficientMap φ c v (MvPolynomial.X i) 1
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one hR hz
  have hz : (⟨g (MvPolynomial.X i), g.map_mem (MvPolynomial.isHomogeneous_X R i)⟩ :
      Projective.ProjectivePresentations.coordinateGrading A n 1) = ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X A i⟩ :=
    Subtype.ext (MvPolynomial.map_X φ i)
  have h := ((congrArg P hz).mp hP) hA
  rw [Chart.OverlapMaps.projectiveChartMap_eq_fraction c v i hi hA,
    Chart.OverlapMaps.projectiveChartMap_eq_fraction (c.comp φ) v i hi hR]
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.CoefficientNaturality
