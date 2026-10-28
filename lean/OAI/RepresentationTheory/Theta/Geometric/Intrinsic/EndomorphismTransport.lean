import OAI.RepresentationTheory.Theta.Geometric.PresentedFrameEndomorphism
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.ChernMaps

/-! # Endomorphism Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic

noncomputable section

/-! The actual native fiber transport commutes with every original
family endomorphism on a constructed neighborhood. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : FamilyFrames.NativeFamilyPeriodFrame C)

attribute [local irreducible] FamilyFrames.NativeFamilyPeriodFrame.nativeFiberTransport FamilyFrames.NativeFamilyPeriodFrame.presentedTorusMap

theorem FamilyFrames.NativeFamilyPeriodFrame.nativeFiberTransport_presented (z : FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C (FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C z)) (t : F.CentralTorus) :
    F.nativeFiberTransport z hz hzN P₀ P (F.presentedTorusMap (FamilyFrames.familyChartCenter C) F.center P₀ t) =
      F.presentedTorusMap z hz P t :=
  congrArg (fun f : TopCat.of F.CentralTorus ⟶ TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver) => f.hom t)
    (F.nativePointTransport_square z hz hzN P₀ P)

theorem FamilyFrames.NativeFamilyPeriodFrame.exists_native_endomorphism_transport
    (present : ∀ y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S, ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (G.pullback y.left))
    (k : G.scheme ⟶ G.scheme) [IsMonHom k] :
    let P := fun z => present (FamilyFrames.familyChartParameter C z)
    ∃ U : Set (FamilyFrames.FamilyChartBase C), IsOpen U ∧ FamilyFrames.familyChartCenter C ∈ U ∧
      ∃ (hU : U ⊆ F.neighborhood) (hN : U ⊆ C.charts.charts.neighborhood),
        ∀ (z : U) (v : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (P (FamilyFrames.familyChartCenter C)).variety.toOver),
          AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) z (P z) k)
            (F.nativeFiberTransport z (hU z.property) (hN z.property) (P (FamilyFrames.familyChartCenter C)) (P z) v) =
          F.nativeFiberTransport z (hU z.property) (hN z.property) (P (FamilyFrames.familyChartCenter C)) (P z)
            (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) (FamilyFrames.familyChartCenter C)
              (P (FamilyFrames.familyChartCenter C)) k) v) := by
  let P := fun z => present (FamilyFrames.familyChartParameter C z)
  obtain ⟨V, hVopen, hxV, hV, hcomm⟩ := F.exists_endomorphism_torus_transport (P (FamilyFrames.familyChartCenter C)) k
  let U := V ∩ C.charts.charts.neighborhood
  have hU : U ⊆ F.neighborhood := fun _ hz => hV hz.1
  have hN : U ⊆ C.charts.charts.neighborhood := Set.inter_subset_right
  refine ⟨U, hVopen.inter C.charts.charts.isOpen, ⟨hxV, Family.ChartOpenImage.familyChartCenter_mem C⟩, hU, hN, ?_⟩
  intro z v
  let e₀ := F.presentedTorusHomeomorph (FamilyFrames.familyChartCenter C) F.center (Family.ChartOpenImage.familyChartCenter_mem C)
    (P (FamilyFrames.familyChartCenter C))
  obtain ⟨t, ht⟩ := e₀.surjective v
  have ht' : F.presentedTorusMap (FamilyFrames.familyChartCenter C) F.center (P (FamilyFrames.familyChartCenter C)) t = v :=
    (F.presentedTorusHomeomorph_apply _ _ _ _ t).symm.trans ht
  rw [← ht', F.nativeFiberTransport_presented,
    ← F.centralTorusEndomorphism_presented, F.nativeFiberTransport_presented,
    F.presentedFiberEndomorphism_torus]
  unfold FamilyFrames.NativeFamilyPeriodFrame.presentedTorusMap
  exact congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P z).comparison.hom) (hcomm ⟨z.val, z.property.1⟩ t)

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic
