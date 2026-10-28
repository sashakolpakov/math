import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveCoefficientsId
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Naturality

/-! # Projective Chart Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveChartCoefficients.ProjectiveCoefficients

noncomputable section

/-! Coefficient changes preserve the actual normalized projective-chart maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Naturality

variable {R T B : Type} [CommRing R] [CommRing T] [CommRing B]

theorem gradedMap_X (f : R →+* T) (n : ℕ) (i : Fin (n + 1)) :
    ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n (MvPolynomial.X i) = MvPolynomial.X i := MvPolynomial.map_X f i

def coordinateAwayMap (f : R →+* T) (n : ℕ) (i : Fin (n + 1)) :
    HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing R n i →+* HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing T n i :=
  HomogeneousLocalization.map (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n) (by
    rintro _ ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    change (MvPolynomial.X i : HilbertConstruction.Projective.ProjectivePresentations.coordinateRing T n) ^ k =
      MvPolynomial.map f ((MvPolynomial.X i : HilbertConstruction.Projective.ProjectivePresentations.coordinateRing R n) ^ k)
    rw [map_pow, MvPolynomial.map_X])

theorem coordinateAwayMap_mk (f : R →+* T) (n : ℕ) (i : Fin (n + 1))
    (d : ℕ) (p : HilbertConstruction.Projective.ProjectivePresentations.coordinateRing R n) (hp : p ∈ HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n d) :
    coordinateAwayMap f n i
      (HomogeneousLocalization.Away.mk (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.isHomogeneous_X R i)
        d p (by simpa only [smul_eq_mul, mul_one] using hp)) =
      HomogeneousLocalization.Away.mk (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n) (MvPolynomial.isHomogeneous_X T i)
        d (MvPolynomial.map f p) (by
          change (MvPolynomial.map f p).IsHomogeneous (d • 1)
          simpa only [smul_eq_mul, mul_one] using MvPolynomial.IsHomogeneous.map hp f) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (MvPolynomial.map f p)
    ⟨MvPolynomial.map f ((MvPolynomial.X i : HilbertConstruction.Projective.ProjectivePresentations.coordinateRing R n) ^ d), _⟩ =
    Localization.mk (MvPolynomial.map f p) ⟨(MvPolynomial.X i : HilbertConstruction.Projective.ProjectivePresentations.coordinateRing T n) ^ d, _⟩
  simp only [map_pow, MvPolynomial.map_X]

theorem coordinateAwayMap_evaluation (f : R →+* T) (c : T →+* B)
    {n : ℕ} (v : Fin (n + 1) → B) (i : Fin (n + 1)) (hi : v i = 1) :
    (HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi).comp (coordinateAwayMap f n i) =
      HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation (c.comp f) v i hi := by
  apply RingHom.ext
  intro z
  obtain ⟨d, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.isHomogeneous_X R i) z
  have hp' : p ∈ HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n d := by simpa only [smul_eq_mul, mul_one] using hp
  change HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi (coordinateAwayMap f n i _) = _
  rw [coordinateAwayMap_mk f n i d p hp',
    HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation_mk c v i hi d (MvPolynomial.map f p) ((ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n).map_mem hp'),
    HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation_mk (c.comp f) v i hi d p hp']
  exact MvPolynomial.eval₂_map _ _ _ _

theorem chart_scheme_map_of_eq (f : R →+* T) (n : ℕ) (i : Fin (n + 1))
    (t : HilbertConstruction.Projective.ProjectivePresentations.coordinateRing T n) (ht : ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n (MvPolynomial.X i) = t)
    (htm : t ∈ HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n 1)
    (hpow : Submonoid.powers (MvPolynomial.X i) ≤ (Submonoid.powers t).comap (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n)) :
    Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n) t htm Nat.zero_lt_one ≫ ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap f n =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n) hpow)) ≫
        Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i)
          Nat.zero_lt_one := by
  subst t
  exact Proj.awayι_comp_map (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n) (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap_irrelevant f n)
    Nat.zero_lt_one (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i)

theorem coordinateAwayMap_scheme (f : R →+* T) (n : ℕ) (i : Fin (n + 1)) :
    Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n) (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X T i)
      Nat.zero_lt_one ≫ ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap f n =
    Spec.map (CommRingCat.ofHom (coordinateAwayMap f n i)) ≫
      Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i)
        Nat.zero_lt_one :=
  chart_scheme_map_of_eq f n i (MvPolynomial.X i) (gradedMap_X f n i)
    (MvPolynomial.isHomogeneous_X T i) _

theorem projectiveChartMap_coefficients {X : Scheme.{0}}
    (f : R →+* T) (c : T →+* Γ(X, ⊤)) {n : ℕ}
    (v : Fin (n + 1) → Γ(X, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) :
    HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartMap c v i hi ≫ ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap f n = HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartMap (c.comp f) v i hi := by
  have h : CommRingCat.ofHom (coordinateAwayMap f n i) ≫
      CommRingCat.ofHom (HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi) =
      CommRingCat.ofHom (HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation (c.comp f) v i hi) :=
    congrArg CommRingCat.ofHom (coordinateAwayMap_evaluation f c v i hi)
  let a := X.toSpecΓ
  let b := Spec.map (CommRingCat.ofHom (HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi))
  let t := Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n) (MvPolynomial.X i)
    (show MvPolynomial.X i ∈ HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n 1 from MvPolynomial.isHomogeneous_X T i)
    Nat.zero_lt_one
  let d := Spec.map (CommRingCat.ofHom (coordinateAwayMap f n i))
  let u := Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
    (show MvPolynomial.X i ∈ HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n 1 from MvPolynomial.isHomogeneous_X R i)
    Nat.zero_lt_one
  have hb : b ≫ d = Spec.map (CommRingCat.ofHom (HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation (c.comp f) v i hi)) :=
    (Spec.map_comp _ _).symm.trans (congrArg Spec.map h)
  exact (Category.assoc a (b ≫ t) (ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap f n)).trans
    (congrArg (fun z => a ≫ z) ((Category.assoc b t (ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap f n)).trans
      ((congrArg (fun z => b ≫ z) (coordinateAwayMap_scheme f n i)).trans
        ((Category.assoc b d u).symm.trans (congrArg (fun z => z ≫ u) hb)))))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveChartCoefficients.ProjectiveCoefficients
