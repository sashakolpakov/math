import OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalHypersurfaceCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.TwoGeneratorBlowupCover

/-! # Zero Dimensional Hypersurface Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalHypersurfaceStep.Construction

noncomputable section

/-! The complete dimension-zero coefficient step in the original ambient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  [Algebra ℚ R] [IsNoetherianRing R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- When the chosen smooth coordinate hypersurface has dimension zero, the
intrinsic tangent ideal itself is a permissible smooth center. Its actual
blowup is an isomorphism and its controlled transform is terminal on a proved
finite affine cover. No retraction or supplied resolution sequence is used. -/
theorem zero_dimensional_hypersurface_intrinsic_step
    (D : Derivation k R R) (z : R) (hD : D z = 1)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] [IsReduced (R ⧸ Ideal.span {z})]
    (hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 0) (J : Ideal R) (n : ℕ)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    let I := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
    let Z : I := ⟨z, hz⟩
    J ≤ I ^ (n + 1) ∧ Algebra.Smooth k (R ⧸ I) ∧ IsIso (ReesGrading.Construction.affineBlowupToSpec I) ∧
      ∃ a : I, I = Ideal.span {a.val} ⊔ Ideal.span {z} ∧
        (Proj.basicOpen (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I a) ⊔
          Proj.basicOpen (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I Z) = ⊤) ∧
        ∀ j : Option (ULift.{u} Unit), Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
          (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) (TwoGeneratorBlowupCover.Construction.pairBlowupChartGenerator I a Z j)) n = ⊤ := by
  let I := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  let Z : I := ⟨z, hz⟩
  obtain ⟨hperm, hsmooth⟩ := ZeroDimensionalHypersurfaceCenter.Construction.zero_dimensional_hypersurface_intrinsic_center k D z hD hd J n hz
  have hiso := Locally.PrincipalBlowup.Construction.zero_dimensional_hypersurface_center_blowup_isIso z (Coordinate.Regularity.Construction.coordinate_isRegular D z hD) hd I hz
  obtain ⟨r, hr, hI, hrel⟩ := IdempotentQuotientCenter.Construction.zero_dimensional_hypersurface_center_generators z hd I hz
  let a : I := ⟨r, hr⟩
  have hC : I.map (Ideal.Quotient.mk (Ideal.span {z})) = Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1) :=
    (ZeroDimensionalCanonicalCenter.Construction.zero_dimensional_relative_coefficients_eq_tangent_image k z hd J n).symm
  have ha := IdempotentQuotientTransform.Construction.idempotent_quotient_chart_differential_unit k I J a Z n hperm hz hrel hC
  have hZ := Coefficient.UnitBlowup.Construction.relative_hypersurface_denominator_differential_unit k I J Z n hperm hz
  refine ⟨hperm, hsmooth, hiso, a, hI, TwoGeneratorBlowupCover.Construction.affineBlowup_pair_chart_cover I a Z hI, ?_⟩
  intro j
  cases j with
  | none => exact hZ
  | some _ => exact ha

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalHypersurfaceStep.Construction
