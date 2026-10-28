import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialSheafRestriction
import OAI.AlgebraicGeometry.Resolution.Blowups.ComplexAffineDifferentialIdeal

/-! # Differential Unit Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialUnitGluing.Construction

noncomputable section

/-! Global differential unit ideals detected on the actual affine open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smoothDifferentialIdealSheaf_structure_congr {X : Scheme} (f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [Smooth f] [Smooth g] (h : f = g) (J : X.IdealSheafData) (n : ℕ) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n = Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g J n := by
  subst g
  rfl

theorem affineQuotientKernel_top {R : Type*} [CommRing R] :
    Affine.QuotientKernel.Construction.affineQuotientKernel (⊤ : Ideal R) = ⊤ := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Affine.QuotientKernel.Construction.affineQuotientKernel_idealTop, Ideal.comap_top]
  rfl

/-- An ideal sheaf is the unit ideal if its pullback to every member of
an actual open cover is the unit ideal. -/
theorem idealSheaf_eq_top_of_openCover {X : Scheme} (I : X.IdealSheafData) (C : X.OpenCover)
    (h : ∀ i : C.I₀, I.comap (C.f i) = ⊤) : I = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff I).mp
  apply SetLike.coe_injective
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, y, hy⟩ := C.exists_eq x
  have hpre : y ∈ (I.comap (C.f i)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change C.f i y ∈ I.support
    rwa [hy]
  rw [h i, Scheme.IdealSheafData.support_top] at hpre
  exact hpre

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]

/-- An actual affine chart carrying the algebraic differential unit bound
has unit pullback of the native global differential ideal sheaf. -/
theorem smoothDifferentialIdealSheaf_unit_on_affine (J : X.IdealSheafData) (n : ℕ)
    {R : Type} [CommRing R] [Algebra ℂ R]
    (j : Spec (.of R) ⟶ X) [IsOpenImmersion j]
    (hstructure : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (L : Ideal R)
    (hJ : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel L)
    (hL : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ L n = ⊤) :
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap j = ⊤ := by
  have hsmooth : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) := hstructure ▸ (inferInstanceAs (Smooth (j ≫ f)))
  let : Algebra.Smooth ℂ R := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsmooth)
  rw [Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open, hJ]
  apply (smoothDifferentialIdealSheaf_structure_congr (j ≫ f) (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R)
    hstructure (Affine.QuotientKernel.Construction.affineQuotientKernel L) n).trans
  rw [ComplexAffineDifferentialIdeal.Construction.smoothDifferentialIdealSheaf_affineQuotientKernel, hL]
  exact affineQuotientKernel_top

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialUnitGluing.Construction
