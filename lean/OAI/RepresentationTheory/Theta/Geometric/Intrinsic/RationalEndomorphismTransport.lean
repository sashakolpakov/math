import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.EndomorphismTransport
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.RationalTransport
import OAI.RepresentationTheory.Theta.Geometric.RealPeriodEndomorphisms

/-! # Rational Endomorphism Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic

noncomputable section

/-! The same original rational period transport intertwines the
actual native rational action of every family endomorphism locally. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : FamilyFrames.NativeFamilyPeriodFrame C)

theorem FamilyFrames.NativeFamilyPeriodFrame.exists_rational_endomorphism_transport
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    (k : G.scheme ⟶ G.scheme) [IsMonHom k] :
    let P := fun z => present (FamilyFrames.familyChartParameter C z)
    ∃ U : Set (FamilyFrames.FamilyChartBase C), IsOpen U ∧ FamilyFrames.familyChartCenter C ∈ U ∧
      ∃ (hU : U ⊆ F.neighborhood) (hN : U ⊆ C.charts.charts.neighborhood),
        ∀ (z : U) (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (P (FamilyFrames.familyChartCenter C)).variety),
          AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) z (P z) k)
            (F.nativeRationalTransport z (hU z.property) (hN z.property) (P (FamilyFrames.familyChartCenter C)) (P z) v) =
          F.nativeRationalTransport z (hU z.property) (hN z.property) (P (FamilyFrames.familyChartCenter C)) (P z)
            (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) (FamilyFrames.familyChartCenter C)
              (P (FamilyFrames.familyChartCenter C)) k) v) := by
  let P := fun z => present (FamilyFrames.familyChartParameter C z)
  obtain ⟨U, hUopen, hxU, hU, hN, hcomm⟩ := F.exists_native_endomorphism_transport present k
  refine ⟨U, hUopen, hxU, hU, hN, ?_⟩
  intro z v
  have hs : F.nativePointTransport z (hU z.property) (hN z.property) (P (FamilyFrames.familyChartCenter C)) (P z) ≫
      TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) z (P z) k)) =
    TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C)
      (FamilyFrames.familyChartCenter C) (P (FamilyFrames.familyChartCenter C)) k)) ≫
      F.nativePointTransport z (hU z.property) (hN z.property) (P (FamilyFrames.familyChartCenter C)) (P z) := by
    apply TopCat.ext
    intro t
    exact hcomm z t
  exact RealPeriodEndomorphisms.RealPeriodMaps.rationalMap_endomorphism
    (F.nativeRealTransport z (hN z.property) (P (FamilyFrames.familyChartCenter C)) (P z)).toContinuousLinearMap
    (fun u hu => (F.nativeRealTransport_lattice z (hU z.property) (hN z.property)
      (P (FamilyFrames.familyChartCenter C)) (P z) u).mpr hu)
    (F.nativePointTransport z (hU z.property) (hN z.property) (P (FamilyFrames.familyChartCenter C)) (P z))
    (F.nativeFiberTransport_period z (hU z.property) (hN z.property) (P (FamilyFrames.familyChartCenter C)) (P z))
    (FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) (FamilyFrames.familyChartCenter C) (P (FamilyFrames.familyChartCenter C)) k)
    (FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) z (P z) k) hs v

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic
