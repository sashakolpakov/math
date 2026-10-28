import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse

/-! # Polarized Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparison

noncomputable section

/-! Algebraize a constructed integral polarized comparison of original
native Hodge structures, keeping its rational periods and polarization. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g N : ℕ} {δ : Fin g → ℕ}

structure NativePolarizedComparison
    (A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) where
  periods : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)) ≃ₗ[ℚ]
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B))
  hodge : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)))
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B))) periods.toLinearMap
  integral : ∀ v, v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)) ↔
    periods v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native B.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B))
  polarization : ∀ v w, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm B (periods v) (periods w) = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativePolarizationForm A v w

namespace NativePolarizedComparison
variable {A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (D : NativePolarizedComparison A B)

def algebraicIso : A.abelian.scheme ≅ B.abelian.scheme :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization.polarizedHodgeAbelianIso A B D.periods D.hodge (AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse.isHodgeMap_inverse _ _ D.periods D.hodge) D.integral

instance algebraicIso_group : IsMonHom D.algebraicIso.hom :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization.polarizedHodgeAbelianIso_isMonHom A B D.periods D.hodge (AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse.isHodgeMap_inverse _ _ D.periods D.hodge) D.integral

attribute [local irreducible] NativePolarizedComparison.algebraicIso

theorem algebraicIso_polarization :
    A.polarization.isogeny.hom ≫ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnderlyingIso.dualFamilyIso A.dual B.dual D.algebraicIso).hom =
      D.algebraicIso.hom ≫ B.polarization.isogeny.hom := by
  unfold NativePolarizedComparison.algebraicIso
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization.polarizedHodgeAbelianIso_polarization A B D.periods D.hodge
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.HodgeInverse.isHodgeMap_inverse _ _ D.periods D.hodge) D.integral D.polarization

theorem algebraicIso_rational :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)).hom ≫
      D.algebraicIso.hom ≫ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso B.abelian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation B)).inv) =
        D.periods.toLinearMap := by
  unfold NativePolarizedComparison.algebraicIso AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.HodgeAlgebraization.polarizedHodgeAbelianIso
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HodgeIso.AbelianIntrinsicAdapter.originalHodgeIso_rational _ _ _ _ _ _ _ _

end NativePolarizedComparison

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparison
