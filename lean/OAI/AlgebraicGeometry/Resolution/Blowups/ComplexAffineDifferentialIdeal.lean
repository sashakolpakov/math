import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientKernel

/-! # Complex Affine Differential Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ComplexAffineDifferentialIdeal.Construction

noncomputable section

/-! Exact affine formulas for the global complex differential ideal sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℂ R]

abbrev complexSpecStructure : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ R))

instance complexSpecStructure_smooth [Algebra.Smooth ℂ R] : Smooth (complexSpecStructure R) :=
  (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr inferInstance)

/-- The affine complex scalars on global sections are the original scalars
transported by the canonical spectrum-sections isomorphism. -/
theorem affineComplexScalars_spec_top :
    Affine.ComplexNaturality.Construction.affineComplexScalars (complexSpecStructure R) ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ =
      (Scheme.ΓSpecIso (.of R)).inv.hom.comp (algebraMap ℂ R) := by
  have he : CommRingCat.ofHom
        (Affine.ComplexNaturality.Construction.affineComplexScalars (complexSpecStructure R) ⟨⊤, isAffineOpen_top (Spec (.of R))⟩) =
      CommRingCat.ofHom (algebraMap ℂ R) ≫ (Scheme.ΓSpecIso (.of R)).inv := by
    apply Spec.map_injective
    rw [Affine.ComplexNaturality.Construction.affineComplexScalars_spec, Spec.map_comp, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv]
  exact congrArg CommRingCat.Hom.hom he

variable [Algebra.Smooth ℂ R]

/-- The intrinsic differential ideal sheaf of an affine quotient kernel
is exactly the quotient kernel of the algebraic relative differential ideal. -/
theorem smoothDifferentialIdealSheaf_affineQuotientKernel (J : Ideal R) (n : ℕ) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (complexSpecStructure R) (Affine.QuotientKernel.Construction.affineQuotientKernel J) n =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n) := by
  let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top (Spec (.of R))⟩
  let : Algebra ℂ Γ(Spec (.of R), U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra (complexSpecStructure R) U
  let e : R ≃ₐ[ℂ] Γ(Spec (.of R), U) :=
    { __ := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
      commutes' c := (RingHom.congr_fun (affineComplexScalars_spec_top R) c).symm }
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf_ideal, Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop, Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop]
  exact (Blowups.Smooth.DifferentialEquiv.Construction.smooth_relativeDifferentialIdeal_comap_equiv ℂ e J n).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ComplexAffineDifferentialIdeal.Construction
