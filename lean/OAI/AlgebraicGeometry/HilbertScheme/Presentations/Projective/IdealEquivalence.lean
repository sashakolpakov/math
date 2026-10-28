import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartOverlap

/-! # Ideal Equivalence -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert

noncomputable section

/-!
The correspondence between ideal sheaves on projective space and saturated
homogeneous ideals of its polynomial coordinate ring.
-/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem projective_ideal_chart_map (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData)
    {d e : ℕ} {s t x : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n}
    (hs : s ∈ Hilbert.Polynomial.GradedHilbert.grading R n d) (ht : t ∈ Hilbert.Polynomial.GradedHilbert.grading R n e)
    (hd : 0 < d) (hx : x = s * t) :
    ((J.ideal ⟨Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s,
      Proj.isAffineOpen_basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s hs hd⟩).comap
        (Proj.awayToSection (Hilbert.Polynomial.GradedHilbert.grading R n) s).hom).map
          (HomogeneousLocalization.awayMap (Hilbert.Polynomial.GradedHilbert.grading R n) ht hx) =
      (J.ideal ⟨Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) x,
        Proj.isAffineOpen_basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) x
          (hx ▸ SetLike.mul_mem_graded hs ht) (Nat.add_pos_left hd e)⟩).comap
            (Proj.awayToSection (Hilbert.Polynomial.GradedHilbert.grading R n) x).hom := by
  let U : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).affineOpens :=
    ⟨Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s, Proj.isAffineOpen_basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s hs hd⟩
  let V : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).affineOpens :=
    ⟨Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) x, Proj.isAffineOpen_basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) x
      (hx ▸ SetLike.mul_mem_graded hs ht) (Nat.add_pos_left hd e)⟩
  let a := (Proj.awayToSection (Hilbert.Polynomial.GradedHilbert.grading R n) s).hom
  let b := (Proj.awayToSection (Hilbert.Polynomial.GradedHilbert.grading R n) x).hom
  let r := HomogeneousLocalization.awayMap (Hilbert.Polynomial.GradedHilbert.grading R n) ht hx
  have hVU : V ≤ U := Proj.basicOpen_mono _ _ _ ⟨t, hx⟩
  let ρ := ((Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).presheaf.map (homOfLE hVU).op).hom
  have ha : Function.Bijective a :=
    (Proj.basicOpenIsoAway (Hilbert.Polynomial.GradedHilbert.grading R n) s hs hd).commRingCatIsoToRingEquiv.bijective
  have hb : Function.Bijective b :=
    (Proj.basicOpenIsoAway (Hilbert.Polynomial.GradedHilbert.grading R n) x (hx ▸ SetLike.mul_mem_graded hs ht)
      (Nat.add_pos_left hd e)).commRingCatIsoToRingEquiv.bijective
  have hdiag : b.comp r = ρ.comp a := by
    exact congrArg CommRingCat.Hom.hom (Proj.awayMap_awayToSection (Hilbert.Polynomial.GradedHilbert.grading R n) ht hx)
  change ((J.ideal U).comap a).map r = (J.ideal V).comap b
  rw [← Ideal.comap_map_of_bijective b hb (I := ((J.ideal U).comap a).map r),
    Ideal.map_map, hdiag, ← Ideal.map_map, Ideal.map_comap_of_surjective a ha.2,
    J.map_ideal hVU]

theorem projectiveChartIdeal_compatible (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) :
    ChartOverlap.GradedHilbert.CompatibleChartIdeals (ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal J) := by
  intro i j
  rw [ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal, ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal, ChartOverlap.GradedHilbert.chartOverlapLeft, ChartOverlap.GradedHilbert.chartOverlapRight,
    projective_ideal_chart_map J (isHomogeneous_X R i) (isHomogeneous_X R j)
      Nat.zero_lt_one rfl,
    projective_ideal_chart_map J (isHomogeneous_X R j) (isHomogeneous_X R i)
      Nat.zero_lt_one (mul_comm _ _)]

theorem quotient_chart_kernel_eq_map (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) :
    RingHom.ker (HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i)) =
      I.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i) := by
  classical
  apply le_antisymm
  · intro z hz
    obtain ⟨d, f, hf, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (Hilbert.Polynomial.GradedHilbert.grading R n) (isHomogeneous_X R i) z
    have hf' : f ∈ Hilbert.Polynomial.GradedHilbert.grading R n d := by simpa only [smul_eq_mul, mul_one] using hf
    obtain ⟨k, hk⟩ := (IdealRecovery.GradedHilbert.quotient_coordinateFraction_eq_zero_iff I i d ⟨f, hf'⟩).mp hz
    have hmem := Ideal.mem_map_of_mem (Dehomogenization.GradedHilbert.dehomogenize i) hk
    change IdealRecovery.GradedHilbert.coordinateFraction i d ⟨f, hf'⟩ ∈ I.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i)
    simpa only [map_mul, map_pow, Dehomogenization.GradedHilbert.dehomogenize_self, one_pow, one_mul,
      Dehomogenization.GradedHilbert.dehomogenize_homogeneous i hf'] using hmem
  · apply Ideal.map_le_iff_le_comap.mpr
    intro f hf
    rw [← DirectSum.sum_support_decompose (Hilbert.Polynomial.GradedHilbert.grading R n) f]
    apply Ideal.sum_mem
    intro d _
    change HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i)
      (Dehomogenization.GradedHilbert.dehomogenize i (DirectSum.decompose (Hilbert.Polynomial.GradedHilbert.grading R n) f d).val) = 0
    rw [Dehomogenization.GradedHilbert.dehomogenize_homogeneous i (DirectSum.decompose (Hilbert.Polynomial.GradedHilbert.grading R n) f d).property]
    apply (IdealRecovery.GradedHilbert.quotient_coordinateFraction_eq_zero_iff I i d _).mpr
    exact ⟨0, by simpa only [pow_zero, one_mul] using I.isHomogeneous d hf⟩

theorem coordinateBasicOpen_cover :
    (⨆ i : Fin (n + 1), Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (Hilbert.Polynomial.GradedHilbert.grading R n)).mpr
  intro d hd f hf
  change f ∈ Ideal.span (Set.range (X : Fin (n + 1) → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n))
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro a ha
  have had : a.degree = d := (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support f d).mp hf a ha
  have hex : ∃ i, a i ≠ 0 := by
    by_contra! h
    have haz : a = 0 := Finsupp.ext h
    rw [haz] at had
    simp only [map_zero] at had
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Set.mem_univ i, hi⟩

theorem projectiveQuotient_homogeneousIdealOfSheaf
    (J : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) :
    (Quotient.GradedHilbert.projectiveQuotientInclusion (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J)).ker = J := by
  let U (i : Fin (n + 1)) : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).affineOpens :=
    ⟨Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) (X i),
      Proj.isAffineOpen_basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) (X i) (isHomogeneous_X R i) Nat.zero_lt_one⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U coordinateBasicOpen_cover
  intro i
  apply Ideal.comap_injective_of_surjective (Proj.awayToSection (Hilbert.Polynomial.GradedHilbert.grading R n) (X i)).hom
    (Proj.basicOpenIsoAway (Hilbert.Polynomial.GradedHilbert.grading R n) (X i) (isHomogeneous_X R i)
      Nat.zero_lt_one).commRingCatIsoToRingEquiv.surjective
  rw [← IdealRecovery.GradedHilbert.projective_chart_kernel_eq (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J) Nat.zero_lt_one (X i)
    (isHomogeneous_X R i), quotient_chart_kernel_eq_map]
  exact ChartOverlap.GradedHilbert.chartHomogeneousIdeal_map (ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal J) (projectiveChartIdeal_compatible J) i

/-- Closed subschemes of projective space are represented uniquely by
saturated homogeneous ideals of the polynomial coordinate ring. -/
def saturatedProjectiveIdealEquiv :
    {I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) // Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal} ≃
      (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData where
  toFun I := (Quotient.GradedHilbert.projectiveQuotientInclusion I.val).ker
  invFun J := ⟨ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J, ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf_saturated J⟩
  left_inv I := Subtype.ext (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf_projectiveQuotient I.val I.property)
  right_inv := projectiveQuotient_homogeneousIdealOfSheaf

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert
