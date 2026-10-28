import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartHomogeneousIdeal

/-! # Chart Overlap -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartOverlap.GradedHilbert

noncomputable section

/-!
Compatibility and denominator clearing on pairs of standard projective
charts. Compatible affine ideals are generated locally by the homogeneous
ideal obtained by intersecting their dehomogenization conditions.
-/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def chartOverlapLeft (i j : Fin (n + 1)) :
    HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R n) (X i) →+*
      HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R n) (X i * X j) :=
  HomogeneousLocalization.awayMap (Hilbert.Polynomial.GradedHilbert.grading R n) (isHomogeneous_X R j) rfl

def chartOverlapRight (i j : Fin (n + 1)) :
    HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R n) (X j) →+*
      HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R n) (X i * X j) :=
  HomogeneousLocalization.awayMap (Hilbert.Polynomial.GradedHilbert.grading R n) (isHomogeneous_X R i) (mul_comm _ _)

theorem homogeneous_chart_overlap (i j : Fin (n + 1))
    {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n} {d : ℕ} (hf : f.IsHomogeneous d) :
    chartOverlapRight i j (Dehomogenization.GradedHilbert.dehomogenize j f) =
      chartOverlapRight i j (Dehomogenization.GradedHilbert.dehomogenize j (X i)) ^ d *
        chartOverlapLeft i j (Dehomogenization.GradedHilbert.dehomogenize i f) := by
  rw [Dehomogenization.GradedHilbert.dehomogenize_homogeneous j hf, Dehomogenization.GradedHilbert.dehomogenize_homogeneous i hf, Dehomogenization.GradedHilbert.dehomogenize_X]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow]
  erw [IdealRecovery.GradedHilbert.coordinateFraction, IdealRecovery.GradedHilbert.coordinateFraction, IdealRecovery.GradedHilbert.coordinateFraction,
    chartOverlapRight, chartOverlapLeft, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    pow_one, mul_pow]
  ring

def CompatibleChartIdeals (J : ChartHomogeneousIdeal.GradedHilbert.ChartIdeals R n) : Prop :=
  ∀ i j, (J i).map (chartOverlapLeft i j) = (J j).map (chartOverlapRight i j)

theorem compatible_chart_clear_denominator (J : ChartHomogeneousIdeal.GradedHilbert.ChartIdeals R n) (hJ : CompatibleChartIdeals J)
    (i j : Fin (n + 1)) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n} {d : ℕ} (hf : f.IsHomogeneous d)
    (hfi : Dehomogenization.GradedHilbert.dehomogenize i f ∈ J i) :
    ∃ k : ℕ, Dehomogenization.GradedHilbert.dehomogenize j (X i) ^ k * Dehomogenization.GradedHilbert.dehomogenize j f ∈ J j := by
  let L := HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R n) (X (R := R) i * X j)
  let := (chartOverlapRight (R := R) i j).toAlgebra
  have hloc := HomogeneousLocalization.Away.isLocalization_mul (𝒜 := Hilbert.Polynomial.GradedHilbert.grading R n)
    (f := X j) (g := X i) (x := X i * X j) (d := 1) (e := 1)
    (isHomogeneous_X R j) (isHomogeneous_X R i) (mul_comm (X i) (X j)) (by omega : 1 ≠ 0)
  have helem : HomogeneousLocalization.Away.isLocalizationElem
      (isHomogeneous_X R j) (isHomogeneous_X R i) = Dehomogenization.GradedHilbert.dehomogenize j (X i) := by
    rw [Dehomogenization.GradedHilbert.dehomogenize_X]
    simp only [HomogeneousLocalization.Away.isLocalizationElem, IdealRecovery.GradedHilbert.coordinateFraction, pow_one]
  have : IsLocalization.Away (Dehomogenization.GradedHilbert.dehomogenize (R := R) j (X i)) L := by
    rw [← helem]
    exact hloc
  have hm : chartOverlapRight i j (Dehomogenization.GradedHilbert.dehomogenize j f) ∈ (J j).map (chartOverlapRight i j) := by
    rw [homogeneous_chart_overlap i j hf]
    apply Ideal.mul_mem_left
    rw [← hJ i j]
    exact Ideal.mem_map_of_mem _ hfi
  change algebraMap _ L (Dehomogenization.GradedHilbert.dehomogenize j f) ∈ (J j).map (algebraMap _ L) at hm
  obtain ⟨s, hs, hsf⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers (Dehomogenization.GradedHilbert.dehomogenize (R := R) j (X i))) L (J j) (Dehomogenization.GradedHilbert.dehomogenize j f)).mp hm
  obtain ⟨k, hk⟩ := hs
  rw [← hk] at hsf
  exact ⟨k, hsf⟩

theorem compatible_chart_homogeneous_extension (J : ChartHomogeneousIdeal.GradedHilbert.ChartIdeals R n)
    (hJ : CompatibleChartIdeals J) (i : Fin (n + 1))
    {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n} {d : ℕ} (hf : f.IsHomogeneous d)
    (hfi : Dehomogenization.GradedHilbert.dehomogenize i f ∈ J i) :
    ∃ m : ℕ, X i ^ m * f ∈ (ChartHomogeneousIdeal.GradedHilbert.chartHomogeneousIdeal J).toIdeal := by
  classical
  choose k hk using fun j => compatible_chart_clear_denominator J hJ i j hf hfi
  let m := ∑ j, k j
  refine ⟨m, (ChartHomogeneousIdeal.GradedHilbert.mem_chartHomogeneousIdeal J (d := m + d) ?_).mpr ?_⟩
  · simpa only [one_mul] using ((isHomogeneous_X R i).pow m).mul hf
  · intro j
    have hj : k j ≤ m := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [map_mul, map_pow]
    have heq : Dehomogenization.GradedHilbert.dehomogenize j (X i) ^ m * Dehomogenization.GradedHilbert.dehomogenize j f =
        Dehomogenization.GradedHilbert.dehomogenize j (X i) ^ (m - k j) *
          (Dehomogenization.GradedHilbert.dehomogenize j (X i) ^ k j * Dehomogenization.GradedHilbert.dehomogenize j f) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
    rw [heq]
    exact (J j).mul_mem_left _ (hk j)

theorem chartHomogeneousIdeal_map (J : ChartHomogeneousIdeal.GradedHilbert.ChartIdeals R n) (hJ : CompatibleChartIdeals J)
    (i : Fin (n + 1)) :
    (ChartHomogeneousIdeal.GradedHilbert.chartHomogeneousIdeal J).toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i) = J i := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    exact (Ideal.toIdeal_homogeneousCore_le (Hilbert.Polynomial.GradedHilbert.grading R n) _).trans (iInf_le _ i)
  · intro z hz
    obtain ⟨d, f, hf, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (Hilbert.Polynomial.GradedHilbert.grading R n) (isHomogeneous_X R i) z
    have hf' : f ∈ Hilbert.Polynomial.GradedHilbert.grading R n d := by simpa only [smul_eq_mul, mul_one] using hf
    change IdealRecovery.GradedHilbert.coordinateFraction i d ⟨f, hf'⟩ ∈ J i at hz
    rw [← Dehomogenization.GradedHilbert.dehomogenize_homogeneous i hf'] at hz
    obtain ⟨m, hm⟩ := compatible_chart_homogeneous_extension J hJ i hf' hz
    have hmem := Ideal.mem_map_of_mem (Dehomogenization.GradedHilbert.dehomogenize i) hm
    change IdealRecovery.GradedHilbert.coordinateFraction i d ⟨f, hf'⟩ ∈ (ChartHomogeneousIdeal.GradedHilbert.chartHomogeneousIdeal J).toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i)
    simpa only [map_mul, map_pow, Dehomogenization.GradedHilbert.dehomogenize_self, one_pow, one_mul,
      Dehomogenization.GradedHilbert.dehomogenize_homogeneous i hf'] using hmem

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartOverlap.GradedHilbert
