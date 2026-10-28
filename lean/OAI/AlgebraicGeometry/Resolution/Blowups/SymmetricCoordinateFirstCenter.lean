import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.SymmetricControlPrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceTranslationMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceSheafCenter

/-! # Symmetric Coordinate First Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! An étale-symmetric control-one program on a coordinate subspace starts with its whole smooth subspace or with the empty center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleSymmetric.coordinate_first_center_eq_or_top
    {σ τ : Type} [Fintype σ] [Fintype τ] {Y : Scheme} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (C : (Spec (.of (MvPolynomial (σ ⊕ τ) ℂ))).IdealSheafData) (hC : C ≠ ⊥)
    (hp : Affine.QuotientKernel.Construction.affineQuotientKernel (RingHom.ker Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom) ≤ C ^ 1)
    (hs : Smooth (C.subschemeι ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (MvPolynomial (σ ⊕ τ) ℂ)))
    (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (MvPolynomial (σ ⊕ τ) ℂ)))
    (tail : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix 1 (GlobalBlowup.Data.Construction.globalBlowup C hC)
      (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (MvPolynomial (σ ⊕ τ) ℂ))
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C
        (Affine.QuotientKernel.Construction.affineQuotientKernel (RingHom.ker Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom)) hC 1) Y g K)
    (H : (Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.blowup C hC (by decide) hp hs hbl tail).EtaleSymmetric) :
    C = Affine.QuotientKernel.Construction.affineQuotientKernel (RingHom.ker Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom) ∨ C = ⊤ := by
  apply Coordinate.SubspaceSheafCenter.Construction.coordinate_subspace_invariant_sheaf_center_eq_or_top C (by simpa only [pow_one] using hp)
  intro a
  exact H.head_center_comap C hC (by decide) hp hs hbl tail
    (Coordinate.SubspaceTranslationMap.Construction.coordinateSubspaceTranslationMap a) (Coordinate.SubspaceTranslationMap.Construction.coordinateSubspaceTranslationMap_ground a)
    (Coordinate.SubspaceTranslationMap.Construction.coordinateSubspaceTranslationMap_ideal a)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
