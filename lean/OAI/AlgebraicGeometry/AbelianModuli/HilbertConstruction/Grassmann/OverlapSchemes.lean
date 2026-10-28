import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationChartParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.AffineCharts

/-! # Overlap Schemes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapSchemes

noncomputable section

/-! Actual principal open subschemes representing overlaps of Grassmannian charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {k l : ℕ} (τ : Equiv.Perm (Fin k ⊕ Fin l))

/-- The overlap coordinate algebra is obtained by inverting the universal determinant. -/
def grassmannOverlapCoordinateAlgebra : CommAlgCat.{u} R :=
  CommAlgCat.of R (Localization.Away (Chart.OverlapDeterminants.chartOverlapPolynomial R τ))

/-- The actual affine scheme of points lying in the two quotient charts. -/
def grassmannOverlapScheme : Over (Spec (CommRingCat.of R)) :=
  (algSpec (CommRingCat.of R)).obj (Opposite.op (grassmannOverlapCoordinateAlgebra R τ))

/-- Inclusion of the overlap into the original quotient chart. -/
def grassmannOverlapι : grassmannOverlapScheme R τ ⟶ AffineCharts.grassmannAffineChart R k l :=
  (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom
    (Algebra.algHom R (MvPolynomial (Fin k × Fin l) R)
      (Localization.Away (Chart.OverlapDeterminants.chartOverlapPolynomial R τ)))).op

/-- This inclusion is an actual open immersion of schemes. -/
instance grassmannOverlapι_isOpenImmersion : IsOpenImmersion (grassmannOverlapι R τ).left :=
  inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial (Fin k × Fin l) R) (Localization.Away (Chart.OverlapDeterminants.chartOverlapPolynomial R τ))))))

/-- Its image is exactly the principal open where the overlap determinant is invertible. -/
theorem grassmannOverlapι_opensRange :
    (grassmannOverlapι R τ).left.opensRange = PrimeSpectrum.basicOpen (Chart.OverlapDeterminants.chartOverlapPolynomial R τ) :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (MvPolynomial (Fin k × Fin l) R)) _

/-- Maps to the actual overlap scheme classify precisely the overlap quotient points. -/
def grassmannOverlapSchemeHomEquiv (A : CommAlgCat.{u} R) :
    ((algSpec (CommRingCat.of R)).obj (Opposite.op A) ⟶ grassmannOverlapScheme R τ) ≃
      LocalizationChartParameters.GrassmannOverlapPoint τ A :=
  (algSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.symm.trans
    ((opEquiv _ _).trans
      { toFun := fun f => LocalizationChartParameters.grassmannOverlapAlgHomEquiv R τ A f.hom
        invFun := fun c => CommAlgCat.ofHom ((LocalizationChartParameters.grassmannOverlapAlgHomEquiv R τ A).symm c)
        left_inv := fun f => by
          apply CommAlgCat.hom_ext
          exact (LocalizationChartParameters.grassmannOverlapAlgHomEquiv R τ A).symm_apply_apply f.hom
        right_inv := fun c => (LocalizationChartParameters.grassmannOverlapAlgHomEquiv R τ A).apply_symm_apply c })

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.OverlapSchemes
