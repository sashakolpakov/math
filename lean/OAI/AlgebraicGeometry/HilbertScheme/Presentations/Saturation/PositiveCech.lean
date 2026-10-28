import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.ChartModules
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.TermMaps

/-! # Positive Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.PositiveCech.GradedHilbert

noncomputable section

/-! Saturation preserves every positive homogeneous Čech term and higher exactness, without an augmentation-degree assumption. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.TermMaps.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))

abbrev saturationCechTermMap (d : ℤ) (q : ℕ) :=
  ModuleCech.TermMaps.ProjectiveCech.moduleCechTermMap R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I))
    (ChartModules.GradedHilbert.saturationQuotientMap I) (ChartModules.GradedHilbert.saturationQuotientMap_homogeneous I) d q

theorem saturationCechTermMap_bijective (d : ℤ) (q : ℕ) (hq : 0 < q) :
    Function.Bijective (saturationCechTermMap I d q) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    funext s
    by_cases hs : s.card = q
    · have hne : s.Nonempty := Finset.card_pos.mp (hs.symm ▸ hq)
      exact (ChartModules.GradedHilbert.saturationChartMap_bijective I s hne).1 (congrFun (congrArg Subtype.val hxy) s)
    · rw [x.property.2 s hs, y.property.2 s hs]
  · exact ModuleCech.TermMaps.ProjectiveCech.moduleCechTermMap_surjective R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (ChartModules.GradedHilbert.saturationQuotientMap I)
      (ChartModules.GradedHilbert.saturationQuotientMap_homogeneous I) (ChartModules.GradedHilbert.saturationQuotientMap_surjective I) d q

theorem saturation_positiveCech_exact_iff (d : ℤ) (q : ℕ) :
    Function.Exact (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1))
      (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1 + 1)) ↔
    Function.Exact (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) d (q + 1))
      (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) d (q + 1 + 1)) := by
  apply AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1)).toAddMonoidHom
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1 + 1)).toAddMonoidHom
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) d (q + 1)).toAddMonoidHom
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) d (q + 1 + 1)).toAddMonoidHom
    (saturationCechTermMap I d (q + 1)).toAddMonoidHom
    (saturationCechTermMap I d (q + 1 + 1)).toAddMonoidHom
    (saturationCechTermMap I d (q + 1 + 1 + 1)).toAddMonoidHom
  · apply AddMonoidHom.ext
    intro x
    exact (ModuleCech.TermMaps.ProjectiveCech.moduleCechTermMap_differential R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (ChartModules.GradedHilbert.saturationQuotientMap I)
      (ChartModules.GradedHilbert.saturationQuotientMap_homogeneous I) d (q + 1) x).symm
  · apply AddMonoidHom.ext
    intro x
    exact (ModuleCech.TermMaps.ProjectiveCech.moduleCechTermMap_differential R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (ChartModules.GradedHilbert.saturationQuotientMap I)
      (ChartModules.GradedHilbert.saturationQuotientMap_homogeneous I) d (q + 1 + 1) x).symm
  · exact (saturationCechTermMap_bijective I d (q + 1) (by omega)).2
  · exact saturationCechTermMap_bijective I d (q + 1 + 1) (by omega)
  · exact (saturationCechTermMap_bijective I d (q + 1 + 1 + 1) (by omega)).1

theorem saturationCech_exact_iff (d : ℤ) (q : ℕ) :
    Function.Exact (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q)
      (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1)) ↔
    Function.Exact (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) d q)
      (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
        (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) d (q + 1)) := by
  apply AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q).toAddMonoidHom
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1)).toAddMonoidHom
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) d q).toAddMonoidHom
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) d (q + 1)).toAddMonoidHom
    (saturationCechTermMap I d q).toAddMonoidHom
    (saturationCechTermMap I d (q + 1)).toAddMonoidHom
    (saturationCechTermMap I d (q + 1 + 1)).toAddMonoidHom
  · apply AddMonoidHom.ext
    intro x
    exact (ModuleCech.TermMaps.ProjectiveCech.moduleCechTermMap_differential R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (ChartModules.GradedHilbert.saturationQuotientMap I)
      (ChartModules.GradedHilbert.saturationQuotientMap_homogeneous I) d q x).symm
  · apply AddMonoidHom.ext
    intro x
    exact (ModuleCech.TermMaps.ProjectiveCech.moduleCechTermMap_differential R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (ChartModules.GradedHilbert.saturationQuotientMap I)
      (ChartModules.GradedHilbert.saturationQuotientMap_homogeneous I) d (q + 1) x).symm
  · exact ModuleCech.TermMaps.ProjectiveCech.moduleCechTermMap_surjective R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (Projective.Saturation.GradedHilbert.projectiveSaturation I)) (ChartModules.GradedHilbert.saturationQuotientMap I)
      (ChartModules.GradedHilbert.saturationQuotientMap_homogeneous I) (ChartModules.GradedHilbert.saturationQuotientMap_surjective I) d q
  · exact saturationCechTermMap_bijective I d (q + 1) (by omega)
  · exact (saturationCechTermMap_bijective I d (q + 1 + 1) (by omega)).1

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.PositiveCech.GradedHilbert
