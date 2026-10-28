import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelOrderEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealChartDescent
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Subspace Sheaf Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceSheafCenter.Construction

noncomputable section

/-! The coordinate-subspace center classification holds for native ideal sheaves on affine space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem coordinate_subspace_invariant_sheaf_center_eq_or_top
    {σ τ : Type} [Finite τ]
    (C : (Spec (.of (MvPolynomial (σ ⊕ τ) ℂ))).IdealSheafData)
    (hp : Affine.QuotientKernel.Construction.affineQuotientKernel (RingHom.ker SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom) ≤ C)
    (hC : ∀ a : τ → ℂ,
      C.comap (Spec.map (CommRingCat.ofHom (PolynomialTranslation.Construction.polynomialTranslate (Sum.elim (fun _ => 0) a)).toRingHom)) = C) :
    C = Affine.QuotientKernel.Construction.affineQuotientKernel (RingHom.ker SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom) ∨ C = ⊤ := by
  obtain ⟨I, rfl⟩ := Affine.KernelOrderEquiv.Construction.exists_affineQuotientKernel C
  have hker := (Affine.KernelOrderEquiv.Construction.affineQuotientKernel_le_iff _ _).mp hp
  have hI (a : τ → ℂ) : I.map (PolynomialTranslation.Construction.polynomialTranslate (Sum.elim (fun _ => 0) a)).toRingHom ≤ I := by
    have h := hC a
    rw [Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom] at h
    exact (Affine.KernelOrderEquiv.Construction.affineQuotientKernel_le_iff _ _).mp h.le
  rcases SubspaceIdeal.Construction.coordinate_subspace_invariant_center_eq_or_top I hker hI with h | h
  · exact Or.inl (congrArg Affine.QuotientKernel.Construction.affineQuotientKernel h)
  · right
    rw [h, DifferentialUnitGluing.Construction.affineQuotientKernel_top]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceSheafCenter.Construction
