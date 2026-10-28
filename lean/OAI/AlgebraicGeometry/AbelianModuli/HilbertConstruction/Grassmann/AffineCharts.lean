import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartRepresentability
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Affine Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.AffineCharts

noncomputable section

/-! The actual affine schemes parametrizing finite-free Grassmannian quotient charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (k l : ℕ)

/-- The affine scheme of matrix coordinates for one Grassmannian chart. -/
def grassmannAffineChart : Over (Spec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).obj (Opposite.op (ChartRepresentability.grassmannChartCoordinateAlgebra R k l))

instance grassmannAffineChart_isAffine : IsAffine (grassmannAffineChart R k l).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin k × Fin l) R))))

/-- The chart is smooth over its coefficient ring. -/
theorem grassmannAffineChart_smooth : Smooth (grassmannAffineChart R k l).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap R (MvPolynomial (Fin k × Fin l) R))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr
    (show Algebra.Smooth R (MvPolynomial (Fin k × Fin l) R) from ⟨inferInstance, inferInstance⟩)

/-- Maps of affine test schemes into the chart classify precisely the quotient-chart points. -/
def grassmannAffineChartHomEquiv (A : CommAlgCat.{u} R) :
    ((algSpec (CommRingCat.of R)).obj (Opposite.op A) ⟶ grassmannAffineChart R k l) ≃
      Charts.GrassmannChart A (Fin l → A) k :=
  (algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.symm.trans
    ((opEquiv _ _).trans (ChartRepresentability.grassmannChartCorepresentable R k l).homEquiv)

/-- A prescribed quotient in the chart determines a unique map to the actual affine chart scheme. -/
theorem grassmannAffineChart_existsUnique_map (A : CommAlgCat.{u} R)
    (c : Charts.GrassmannChart A (Fin l → A) k) :
    ∃! f : (algSpec (CommRingCat.of R)).obj (Opposite.op A) ⟶ grassmannAffineChart R k l,
      grassmannAffineChartHomEquiv R k l A f = c := by
  let e := grassmannAffineChartHomEquiv R k l A
  refine ⟨e.symm c, e.apply_symm_apply c, ?_⟩
  intro f hf
  exact e.injective (hf.trans (e.apply_symm_apply c).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.AffineCharts
