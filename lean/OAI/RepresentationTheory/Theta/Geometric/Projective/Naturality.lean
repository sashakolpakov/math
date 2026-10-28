import OAI.RepresentationTheory.Theta.Geometric.Projective.ChartSchemes

/-! # Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.Naturality.RelativeProjective

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R S : Type} [CommRing R] [CommRing S]

def chartCoefficientMap (f : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    Charts.RelativeProjective.projectiveChartRing R n i →+* Charts.RelativeProjective.projectiveChartRing S n i :=
  HomogeneousLocalization.map (Map.RelativeProjective.coordinateGradedMap f n) (by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, by simp⟩)

theorem chartCoefficientMap_mk (f : R →+* S) (n : ℕ) (i : Fin (n + 1))
    (k : ℕ) (p : Charts.RelativeProjective.homogeneousCoordinateRing R n) (hp : p ∈ Charts.RelativeProjective.projectiveGrading R n (k • 1)) :
    chartCoefficientMap f n i
      (HomogeneousLocalization.Away.mk (Charts.RelativeProjective.projectiveGrading R n)
        (Charts.RelativeProjective.projectiveVariable_homogeneous R n i) k p hp) =
      HomogeneousLocalization.Away.mk (Charts.RelativeProjective.projectiveGrading S n)
        (Charts.RelativeProjective.projectiveVariable_homogeneous S n i) k (MvPolynomial.map f p) (hp.map f) := by
  simp [chartCoefficientMap, HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk]
  rfl

theorem chartCoefficientMap_dehomogenize (f : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    (Charts.RelativeProjective.projectiveChartToPolynomial S n i).comp (chartCoefficientMap f n i) =
      (MvPolynomial.map f).comp (Charts.RelativeProjective.projectiveChartToPolynomial R n i) := by
  apply RingHom.ext
  intro x
  obtain ⟨k, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (Charts.RelativeProjective.projectiveGrading R n) (Charts.RelativeProjective.projectiveVariable_homogeneous R n i) x
  simp only [RingHom.comp_apply, chartCoefficientMap_mk, Charts.RelativeProjective.projectiveChartToPolynomial_mk]
  rw [Charts.RelativeProjective.projectiveChartToPolynomial_mk S n i k (MvPolynomial.map f p) (hp.map f)]
  have h : (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i).comp
      (MvPolynomial.map f) = (MvPolynomial.map f).comp
        (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro j
      by_cases hj : j = i <;> simp [hj]
  exact RingHom.congr_fun h p

theorem awayChart_map_of_eq (f : R →+* S) (n : ℕ)
    (u : Charts.RelativeProjective.homogeneousCoordinateRing R n) (v : Charts.RelativeProjective.homogeneousCoordinateRing S n)
    (hu : u ∈ Charts.RelativeProjective.projectiveGrading R n 1) (hv : v ∈ Charts.RelativeProjective.projectiveGrading S n 1)
    (he : Map.RelativeProjective.coordinateGradedMap f n u = v) :
    Proj.awayι (Charts.RelativeProjective.projectiveGrading S n) v hv Nat.zero_lt_one ≫ Map.RelativeProjective.coefficientMap f n =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map (Map.RelativeProjective.coordinateGradedMap f n)
        (P := Submonoid.powers u) (Q := Submonoid.powers v) (by
          rintro _ ⟨k, rfl⟩
          exact ⟨k, by simp [he]⟩))) ≫
        Proj.awayι (Charts.RelativeProjective.projectiveGrading R n) u hu Nat.zero_lt_one := by
  subst v
  exact Proj.awayι_comp_map (Map.RelativeProjective.coordinateGradedMap f n) (Map.RelativeProjective.irrelevant_le_coordinateMap f n)
    Nat.zero_lt_one u hu

theorem awayChart_coefficientMap (f : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    Proj.awayι (Charts.RelativeProjective.projectiveGrading S n) (MvPolynomial.X i)
      (Charts.RelativeProjective.projectiveVariable_homogeneous S n i) Nat.zero_lt_one ≫ Map.RelativeProjective.coefficientMap f n =
    Spec.map (CommRingCat.ofHom (chartCoefficientMap f n i)) ≫
      Proj.awayι (Charts.RelativeProjective.projectiveGrading R n) (MvPolynomial.X i)
        (Charts.RelativeProjective.projectiveVariable_homogeneous R n i) Nat.zero_lt_one := by
  exact awayChart_map_of_eq f n (MvPolynomial.X i) (MvPolynomial.X i)
    (Charts.RelativeProjective.projectiveVariable_homogeneous R n i) (Charts.RelativeProjective.projectiveVariable_homogeneous S n i)
    (Map.RelativeProjective.coordinateGradedMap_X f n i)

theorem projectiveAffineChartMap_coefficientMap (f : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    ChartSchemes.RelativeProjective.projectiveAffineChartMap S n i ≫ Map.RelativeProjective.coefficientMap f n =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map f :
        Charts.RelativeProjective.projectiveChartPolynomial R n i →+* Charts.RelativeProjective.projectiveChartPolynomial S n i)) ≫
        ChartSchemes.RelativeProjective.projectiveAffineChartMap R n i := by
  unfold ChartSchemes.RelativeProjective.projectiveAffineChartMap
  rw [ChartSchemes.RelativeProjective.projectiveCoordinateIsoSpec_inv_ι, ChartSchemes.RelativeProjective.projectiveCoordinateIsoSpec_inv_ι,
    Category.assoc, awayChart_coefficientMap, ← Category.assoc, ← Spec.map_comp]
  rw [← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext (chartCoefficientMap_dehomogenize f n i)

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.Naturality.RelativeProjective
