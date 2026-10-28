import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.PointClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualHolomorphicInjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel

/-! # Descended Holomorphic Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Exact native holomorphic classes of the algebraically descended
theta family on the constructed dual model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP)) (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)).sheaf)

local instance IsogenyKernel.ReferenceLatticeIsogeny.descendedHolomorphic_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance IsogenyKernel.ReferenceLatticeIsogeny.descendedHolomorphic_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance IsogenyKernel.ReferenceLatticeIsogeny.descendedHolomorphic_dualIntegral : IsIntegral D.abelian.toOver.left := D.abelian.variety.property
local instance IsogenyKernel.ReferenceLatticeIsogeny.descendedHolomorphic_dualSmooth : Smooth D.abelian.toOver.hom := D.abelian.variety.presentation.smooth
local instance IsogenyKernel.ReferenceLatticeIsogeny.descendedHolomorphic_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

include hdeg hf hg recover in
theorem IsogenyKernel.ReferenceLatticeIsogeny.descendedThetaHolomorphicClass_mk (a : F.periodData.space) :
    Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (IntrinsicPointLine.nativePointFamilyLine Q (D.period (QuotientAddGroup.mk a))) =
      M.translationHolomorphicClass (-a) := by
  have hp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom (M.vectorPeriod a) = D.period (QuotientAddGroup.mk a) :=
    p.period_eq (QuotientAddGroup.mk a)
  have hc := (IntrinsicPointLine.nativePointFamilyLine_baseChange Q p.isogeny.hom (M.vectorPeriod a)).symm.trans
    (IntrinsicPointLine.nativePointFamilyLine_congr _ _ recover (M.vectorPeriod a))
  rw [hp] at hc
  exact (congrArg (Intrinsic.HolomorphicIsoClass.nativeHolomorphicPicardClass M.abelian.variety) hc).trans
    (M.thetaPointDifference_holomorphicClass U V f g hf hg hdeg a)

include hdeg hf hg recover in
theorem IsogenyKernel.ReferenceLatticeIsogeny.descendedThetaHolomorphicClass (q : (F.dualPeriodData hP).periodTorus) :
    Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (IntrinsicPointLine.nativePointFamilyLine Q (D.period q)) =
      -M.dualTorusHolomorphicHom q := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact (p.descendedThetaHolomorphicClass_mk U V hdeg f g hf hg Q recover a).trans
    (map_neg M.translationHolomorphicHom a)

include hdeg hf hg recover in
theorem IsogenyKernel.ReferenceLatticeIsogeny.descendedThetaHolomorphicClass_injective :
    Function.Injective (fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver =>
      Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (IntrinsicPointLine.nativePointFamilyLine Q x)) := by
  intro x y h
  apply D.period.symm.injective
  apply M.dualTorusHolomorphicHom_injective
  apply neg_injective
  have hx := p.descendedThetaHolomorphicClass U V hdeg f g hf hg Q recover (D.period.symm x)
  have hy := p.descendedThetaHolomorphicClass U V hdeg f g hf hg Q recover (D.period.symm y)
  rw [D.period.apply_symm_apply] at hx hy
  exact hx.symm.trans (h.trans hy)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
