import OAI.RepresentationTheory.Theta.Geometric.Projective.Naturality
import OAI.RepresentationTheory.Theta.Geometric.PolynomialBaseChange

/-! # Base Change -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.BaseChange.RelativeProjective

noncomputable section

/-! Relative projective space commutes with extension of coefficients.
The proof uses the actual standard affine scheme charts and their native
pullback squares, then glues the universal property. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R S : Type} [CommRing R] [CommRing S]

abbrev awayChart (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :=
  Proj.awayι (Charts.RelativeProjective.projectiveGrading R n) (MvPolynomial.X i)
    (Charts.RelativeProjective.projectiveVariable_homogeneous R n i) Nat.zero_lt_one

theorem coordinateCover_map (R : Type) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    (Map.RelativeProjective.projectiveCoordinateAffineCover R n).openCover.f i = awayChart R n i := rfl

theorem chartCoefficient_isPullback (f : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (Naturality.RelativeProjective.chartCoefficientMap f n i)))
      (awayChart S n i ≫ Map.RelativeProjective.projectiveSpaceToBase S n)
      (awayChart R n i ≫ Map.RelativeProjective.projectiveSpaceToBase R n)
      (Spec.map (CommRingCat.ofHom f)) := by
  apply (PolynomialBaseChange.RelativeProjective.polynomial_isPullback f n i).of_iso
    (Scheme.Spec.mapIso (Charts.RelativeProjective.projectiveChartRingEquiv S n i).toCommRingCatIso.op)
    (Scheme.Spec.mapIso (Charts.RelativeProjective.projectiveChartRingEquiv R n i).toCommRingCatIso.op)
    (Iso.refl _) (Iso.refl _)
  · change Spec.map (CommRingCat.ofHom (MvPolynomial.map f)) ≫
        Spec.map (CommRingCat.ofHom (Charts.RelativeProjective.projectiveChartToPolynomial R n i)) =
      Spec.map (CommRingCat.ofHom (Charts.RelativeProjective.projectiveChartToPolynomial S n i)) ≫
        Spec.map (CommRingCat.ofHom (Naturality.RelativeProjective.chartCoefficientMap f n i))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (Naturality.RelativeProjective.chartCoefficientMap_dehomogenize f n i).symm
  · change ChartSchemes.RelativeProjective.projectiveChartPolynomialToBase S n i ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom (Charts.RelativeProjective.projectiveChartToPolynomial S n i)) ≫
        (awayChart S n i ≫ Map.RelativeProjective.projectiveSpaceToBase S n)
    rw [Category.comp_id, Map.RelativeProjective.projectiveSpaceToBase_chart, ← Spec.map_comp]
    unfold ChartSchemes.RelativeProjective.projectiveChartPolynomialToBase
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact (Charts.RelativeProjective.projectiveChartToPolynomial_constants S n i c).symm
  · change ChartSchemes.RelativeProjective.projectiveChartPolynomialToBase R n i ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom (Charts.RelativeProjective.projectiveChartToPolynomial R n i)) ≫
        (awayChart R n i ≫ Map.RelativeProjective.projectiveSpaceToBase R n)
    rw [Category.comp_id, Map.RelativeProjective.projectiveSpaceToBase_chart, ← Spec.map_comp]
    unfold ChartSchemes.RelativeProjective.projectiveChartPolynomialToBase
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact (Charts.RelativeProjective.projectiveChartToPolynomial_constants R n i c).symm
  · simp

theorem chartOpen_isPullback (f : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (Naturality.RelativeProjective.chartCoefficientMap f n i)))
      (awayChart S n i) (awayChart R n i) (Map.RelativeProjective.coefficientMap f n) := by
  apply IsOpenImmersion.isPullback
  · exact Naturality.RelativeProjective.awayChart_coefficientMap f n i
  · simp only [awayChart, Proj.opensRange_awayι]
    exact Map.RelativeProjective.coefficientMap_preimage f n i

theorem coefficient_isPullback (f : R →+* S) (n : ℕ) :
    IsPullback (Map.RelativeProjective.coefficientMap f n) (Map.RelativeProjective.projectiveSpaceToBase S n)
      (Map.RelativeProjective.projectiveSpaceToBase R n) (Spec.map (CommRingCat.ofHom f)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (Map.RelativeProjective.projectiveCoordinateAffineCover R n).openCover
  intro i
  let H := (chartOpen_isPullback f n i).flip
  apply (chartCoefficient_isPullback f n i).of_iso H.isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change Spec.map (CommRingCat.ofHom (Naturality.RelativeProjective.chartCoefficientMap f n i)) ≫ 𝟙 _ =
      H.isoPullback.hom ≫ pullback.snd (Map.RelativeProjective.coefficientMap f n) (awayChart R n i)
    simpa only [Category.comp_id] using H.isoPullback_hom_snd.symm
  · change (awayChart S n i ≫ Map.RelativeProjective.projectiveSpaceToBase S n) ≫ 𝟙 _ =
      H.isoPullback.hom ≫ (pullback.fst (Map.RelativeProjective.coefficientMap f n) (awayChart R n i) ≫
        Map.RelativeProjective.projectiveSpaceToBase S n)
    simpa only [Category.comp_id, Category.assoc] using
      (congrArg (fun a => a ≫ Map.RelativeProjective.projectiveSpaceToBase S n) H.isoPullback_hom_fst).symm
  · change (awayChart R n i ≫ Map.RelativeProjective.projectiveSpaceToBase R n) ≫ 𝟙 _ =
      𝟙 _ ≫ (awayChart R n i ≫ Map.RelativeProjective.projectiveSpaceToBase R n)
    simp
  · simp

def projectiveBaseChangeIso (f : R →+* S) (n : ℕ) :
    Map.RelativeProjective.projectiveSpace S n ≅ pullback (Map.RelativeProjective.projectiveSpaceToBase R n) (Spec.map (CommRingCat.ofHom f)) :=
  (coefficient_isPullback f n).isoPullback

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.BaseChange.RelativeProjective
