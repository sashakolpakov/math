import OAI.AlgebraicGeometry.Resolution.Blowups.Global.Homogenization
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelSums
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialUnitGluing

/-! # Homogenization Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizationRestriction.Construction

noncomputable section

/-! Global homogenization agrees with its intrinsic ring formula on every actual open chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smoothHomogenizedIdealSheaf_structure_congr {X : Scheme} (f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [Smooth f] [Smooth g] (h : f = g) (J : X.IdealSheafData) (n : ℕ) :
    Homogenization.Construction.smoothHomogenizedIdealSheaf f J n = Homogenization.Construction.smoothHomogenizedIdealSheaf g J n := by
  subst g
  rfl

theorem smoothHomogenizedIdealSheaf_comap_open {X Y : Scheme}
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : Y.IdealSheafData) (n : ℕ)
    (g : X ⟶ Y) [IsOpenImmersion g] :
    (Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap g =
      Homogenization.Construction.smoothHomogenizedIdealSheaf (g ≫ f) (J.comap g) n := by
  simp only [Homogenization.Construction.smoothHomogenizedIdealSheaf, Affine.KernelSums.Construction.idealSheaf_comap_iSup,
    IdealSheaf.ProductRestriction.Construction.idealSheaf_comap_mul_open, IdealSheaf.ColonRestriction.Construction.idealSheaf_comap_pow_open, Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open]

theorem smoothHomogenizedIdealSheaf_affineQuotientKernel
    (R : Type) [CommRing R] [Algebra ℂ R] [Algebra.Smooth ℂ R] (J : Ideal R) (n : ℕ) :
    Homogenization.Construction.smoothHomogenizedIdealSheaf (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (Affine.QuotientKernel.Construction.affineQuotientKernel J) n =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ J n) := by
  simp only [Homogenization.Construction.smoothHomogenizedIdealSheaf, Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal, Affine.KernelSums.Construction.affineQuotientKernel_iSup,
    IdealSheaf.ProductRestriction.Construction.affineQuotientKernel_mul, Affine.QuotientKernel.Construction.affineQuotientKernel_pow, ComplexAffineDifferentialIdeal.Construction.smoothDifferentialIdealSheaf_affineQuotientKernel]

theorem smoothHomogenizedIdealSheaf_comap_affine
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (n : ℕ)
    {R : Type} [CommRing R] [Algebra ℂ R] (j : Spec (.of R) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (L : Ideal R)
    (hJ : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel L) :
    (Homogenization.Construction.smoothHomogenizedIdealSheaf f J n).comap j =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ L n) := by
  have hs : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) := hj ▸ (inferInstanceAs (Smooth (j ≫ f)))
  let : Algebra.Smooth ℂ R := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)
  rw [smoothHomogenizedIdealSheaf_comap_open, hJ]
  exact (smoothHomogenizedIdealSheaf_structure_congr (j ≫ f) _ hj _ n).trans
    (smoothHomogenizedIdealSheaf_affineQuotientKernel R L n)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.HomogenizationRestriction.Construction
