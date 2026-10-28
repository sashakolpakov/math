import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.CentralIdentification

/-! # Presented Frame Endomorphism -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original family endomorphism in the exact native presentation
of each fiber, retaining its commuting fixed-torus square. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (k : G.scheme ⟶ G.scheme) :
    P.variety.toOver ⟶ P.variety.toOver :=
  P.comparison.inv ≫ ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (Intrinsic.FamilyFrames.familyChartParameter C z) ≫ P.comparison.hom

instance Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism_group (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (k : G.scheme ⟶ G.scheme) [IsMonHom k] :
    IsMonHom (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) z P k) := by
  let : IsMonHom (ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (Intrinsic.FamilyFrames.familyChartParameter C z)) := ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism_group S G k _
  unfold Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism
  infer_instance

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism_torus (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (k : G.scheme ⟶ G.scheme) (t : F.CentralTorus) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) z P k) (F.presentedTorusMap z hz P t) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (Intrinsic.FamilyFrames.familyChartParameter C z)) (F.torusFiberMap z hz t)) := by
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P.comparison.inv ≫ _ ≫ P.comparison.hom)
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom (F.torusFiberMap z hz t)) = _
  rw [← AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusEndomorphism_presented
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (k : G.scheme ⟶ G.scheme) (t : F.CentralTorus) :
    F.presentedTorusMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center P (F.centralTorusEndomorphism P k t) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedFiberEndomorphism (C := C) (Intrinsic.FamilyFrames.familyChartCenter C) P k)
        (F.presentedTorusMap (Intrinsic.FamilyFrames.familyChartCenter C) F.center P t) := by
  rw [F.presentedFiberEndomorphism_torus]
  exact congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom) (F.centralTorusEndomorphism_square P k t)

end

end OAI.RepresentationTheory.Theta.Geometric
