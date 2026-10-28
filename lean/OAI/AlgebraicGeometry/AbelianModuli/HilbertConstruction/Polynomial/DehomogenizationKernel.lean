import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.Homogenization
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Dehomogenization Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.DehomogenizationKernel.PolynomialHomogenization

noncomputable section

/-! Setting the extra homogeneous coordinate to one has exactly the expected kernel. -/

open _root_.MvPolynomial

variable {R σ : Type*} [CommRing R]

theorem dehomogenizeOption_surjective :
    Function.Surjective (Homogenization.PolynomialHomogenization.dehomogenizeOption (σ := σ) R) :=
  fun p => ⟨rename some p, Homogenization.PolynomialHomogenization.dehomogenizeOption_rename_some p⟩

theorem dehomogenizeOption_kernel :
    RingHom.ker (Homogenization.PolynomialHomogenization.dehomogenizeOption (σ := σ) R) =
      Ideal.span {(X none - 1 : MvPolynomial (Option σ) R)} := by
  let J : Ideal (MvPolynomial (Option σ) R) := Ideal.span {X none - 1}
  have hX : Ideal.Quotient.mk J (X none) = 1 := by
    apply sub_eq_zero.mp
    rw [← map_one (Ideal.Quotient.mk J), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton (X none - 1)))
  have hnorm : ((Ideal.Quotient.mk J).comp (rename some).toRingHom).comp
      (Homogenization.PolynomialHomogenization.dehomogenizeOption (σ := σ) R) = Ideal.Quotient.mk J := by
    apply ringHom_ext
    · intro r
      simp
    · intro i
      cases i with
      | none => simpa only [RingHom.comp_apply, Homogenization.PolynomialHomogenization.dehomogenizeOption_X_none, map_one] using hX.symm
      | some i => simp
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← hnorm]
    change ((Ideal.Quotient.mk J).comp (rename some).toRingHom)
      (Homogenization.PolynomialHomogenization.dehomogenizeOption R p) = 0
    rw [show Homogenization.PolynomialHomogenization.dehomogenizeOption R p = 0 from hp, map_zero]
  · apply Ideal.span_le.mpr
    rintro p (rfl : p = X none - 1)
    change Homogenization.PolynomialHomogenization.dehomogenizeOption R (X none - 1) = 0
    simp

theorem dehomogenizeOption_comap_map (I : Ideal (MvPolynomial (Option σ) R)) :
    Ideal.comap (Homogenization.PolynomialHomogenization.dehomogenizeOption R) (Ideal.map (Homogenization.PolynomialHomogenization.dehomogenizeOption R) I) =
      I ⊔ Ideal.span {(X none - 1 : MvPolynomial (Option σ) R)} := by
  rw [Ideal.comap_map_of_surjective _ dehomogenizeOption_surjective,
    ← RingHom.ker_eq_comap_bot, dehomogenizeOption_kernel]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.DehomogenizationKernel.PolynomialHomogenization
