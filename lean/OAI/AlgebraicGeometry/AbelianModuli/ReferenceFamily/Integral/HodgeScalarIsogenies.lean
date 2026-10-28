import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HodgeFullness
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods
import OAI.RepresentationTheory.Theta.Geometric.Torus.Isogeny

/-! # Hodge Scalar Isogenies -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.HodgeScalarIsogenies.IntrinsicLinearMaps

noncomputable section

/-! Complementary integral Hodge maps algebraize with their exact
prescribed scalar multiplier. No further denominator is introduced.
Both algebraic maps and both scalar composition identities are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B)
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)
    (hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B) f)
    (hv : ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure B) (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure A) v)
    (hΛf : ∀ x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A, f x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods B)
    (hΛv : ∀ x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods B, v x ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods A)
    (n : ℕ)

theorem nativeIntegralHodgeMaps_scalar_composition
    (hfv : v.comp f = n • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A)) :
    Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛf ≫ Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend v hv hΛv = (𝟙 A.toOver) ^ n := by
  apply Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.HodgeFullness.IntrinsicLinearMaps.rationalLift_nativeHodgeDescend, Intrinsic.HodgeFullness.IntrinsicLinearMaps.rationalLift_nativeHodgeDescend,
    Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps.rationalLift_multiplication]
  exact hfv

theorem nativeIntegralHodgeMaps_both_finite_etale
    (hn : 0 < n)
    (hfv : v.comp f = n • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A))
    (hvf : f.comp v = n • (LinearMap.id : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B →ₗ[ℚ] Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B)) :
    IsFinite (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛf).left ∧ Etale (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛf).left ∧
      Surjective (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛf).left ∧
    IsFinite (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend v hv hΛv).left ∧ Etale (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend v hv hΛv).left ∧
      Surjective (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend v hv hΛv).left := by
  have h₁ := nativeIntegralHodgeMaps_scalar_composition f v hf hv hΛf hΛv n hfv
  have h₂ := nativeIntegralHodgeMaps_scalar_composition v f hv hf hΛv hΛf n hvf
  have hfgeom := RepresentationTheory.Theta.Geometric.Torus.Isogeny.finite_etale_surjective_of_two_complements A B
    (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛf) (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend v hv hΛv) n hn h₁ h₂
  have hvgeom := RepresentationTheory.Theta.Geometric.Torus.Isogeny.finite_etale_surjective_of_two_complements B A
    (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend v hv hΛv) (Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛf) n hn h₂ h₁
  exact ⟨hfgeom.1, hfgeom.2.1, hfgeom.2.2, hvgeom.1, hvgeom.2.1, hvgeom.2.2⟩

theorem nativeIntegralHodgeMap_intertwines
    (a : A.toOver ⟶ A.toOver) (b : B.toOver ⟶ B.toOver) [IsMonHom a] [IsMonHom b]
    (hab : f.comp (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift a) = (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift b).comp f) :
    a ≫ Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛf = Intrinsic.HodgeFullness.IntrinsicLinearMaps.nativeHodgeDescend f hf hΛf ≫ b := by
  apply Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_faithful
  rw [Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, Intrinsic.HodgeFullness.IntrinsicLinearMaps.rationalLift_nativeHodgeDescend]
  exact hab

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.HodgeScalarIsogenies.IntrinsicLinearMaps
