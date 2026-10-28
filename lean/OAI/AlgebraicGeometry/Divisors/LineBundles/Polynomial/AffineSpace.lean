import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Projection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Affine Space -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.AffineSpace.BundleCycles

noncomputable section

/-! # LineBundleCycles: the ordinary polynomial spectrum is the actual relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R]

def polynomialAffineSpaceEquiv : Spec (.of (Polynomial R)) ≅ AffineSpace PUnit (Spec (.of R)) :=
  Scheme.Spec.mapIso (MvPolynomial.uniqueAlgEquiv R PUnit).toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso PUnit (.of R)).symm

theorem polynomialAffineSpaceEquiv_over :
    (polynomialAffineSpaceEquiv R).hom ≫ (AffineSpace PUnit (Spec (.of R)) ↘ Spec (.of R)) =
      Projection.BundleCycles.polynomialProjection R := by
  have h : CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial PUnit R) ≫
      (MvPolynomial.uniqueAlgEquiv R PUnit).toRingEquiv.toCommRingCatIso.hom =
        CommRingCat.ofHom (algebraMap R (Polynomial R)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (MvPolynomial.uniqueAlgEquiv R PUnit).commutes a
  change (Spec.map (MvPolynomial.uniqueAlgEquiv R PUnit).toRingEquiv.toCommRingCatIso.hom ≫
    (AffineSpace.SpecIso PUnit (.of R)).inv) ≫ _ = _
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, h]
  rfl

instance polynomialProjection_smooth : Smooth (Projection.BundleCycles.polynomialProjection R) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr
    (Algebra.Smooth.mk inferInstance inferInstance))

instance polynomialProjection_geometricallyIntegral : GeometricallyIntegral (Projection.BundleCycles.polynomialProjection R) := by
  constructor
  intro K hK y Z a b h
  let e := polynomialAffineSpaceEquiv R
  apply (show GeometricallyIntegral (AffineSpace PUnit (Spec (.of R)) ↘ Spec (.of R)) from
    inferInstance).geometrically_isIntegral y (a ≫ e.hom) b
  apply h.of_iso (.refl _) e (.refl _) (.refl _)
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · exact (Category.comp_id _).trans (polynomialAffineSpaceEquiv_over R).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem polynomialPrimePoint_eq_fiberGeneric (p : Spec (.of R)) :
    Projection.BundleCycles.polynomialPrimePoint R p = Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Projection.BundleCycles.polynomialProjection R) p := by
  apply Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_unique _ _ _ (Projection.BundleCycles.polynomialPrimePoint_projection R p)
  intro P hP
  exact (congrArg (Projection.BundleCycles.polynomialPrimePoint R) hP) ▸ Projection.BundleCycles.polynomialPrimePoint_specializes R P

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.AffineSpace.BundleCycles
