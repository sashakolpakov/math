import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.RationalEndomorphismTransport

/-! # Endomorphism Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Finitely many original family endomorphisms are retained on one
constructed open neighborhood in the same full rational period frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.exists_finite_rational_endomorphism_transport
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    {I : Type} [Finite I] (k : I → (G.scheme ⟶ G.scheme)) [∀ i, IsMonHom (k i)] :
    let P := fun z => present (Intrinsic.FamilyFrames.familyChartParameter C z)
    ∃ U : Set (Intrinsic.FamilyFrames.FamilyChartBase C), IsOpen U ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ U ∧
      ∃ (hU : U ⊆ F.neighborhood) (hN : U ⊆ C.charts.charts.neighborhood),
        ∀ (z : U) (i : I) (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (P (Intrinsic.FamilyFrames.familyChartCenter C)).variety),
          AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) z (P z) (k i))
            (F.nativeRationalTransport z (hU z.property) (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z) v) =
          F.nativeRationalTransport z (hU z.property) (hN z.property) (P (Intrinsic.FamilyFrames.familyChartCenter C)) (P z)
            (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) (Intrinsic.FamilyFrames.familyChartCenter C)
              (P (Intrinsic.FamilyFrames.familyChartCenter C)) (k i)) v) := by
  let P := fun z => present (Intrinsic.FamilyFrames.familyChartParameter C z)
  choose U hUopen hxU hU hN hcomm using fun i => F.exists_rational_endomorphism_transport present (k i)
  let V := (F.neighborhood ∩ C.charts.charts.neighborhood) ∩ ⋂ i, U i
  have hVF : V ⊆ F.neighborhood := fun _ hz => hz.1.1
  have hVN : V ⊆ C.charts.charts.neighborhood := fun _ hz => hz.1.2
  have hopen : IsOpen V := (F.isOpen.inter C.charts.charts.isOpen).inter (isOpen_iInter_of_finite hUopen)
  have hcenter : Intrinsic.FamilyFrames.familyChartCenter C ∈ V :=
    ⟨⟨F.center, Family.ChartOpenImage.familyChartCenter_mem C⟩, Set.mem_iInter.mpr hxU⟩
  refine ⟨V, hopen, hcenter, hVF, hVN, ?_⟩
  intro z i v
  exact hcomm i ⟨z.val, Set.mem_iInter.mp z.property.2 i⟩ v

end

end OAI.RepresentationTheory.Theta.Geometric
