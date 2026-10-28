import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PeriodLiftDisplacements
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultTransition

/-! # Translation Sub -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

section

/-! The reference translation potentials glue through the actual
Dolbeault sequence and give a holomorphic unit class with precisely the
original theta translation factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.translationDolbeault_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.translationDolbeault_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem AlgebraicModel.ReferenceAlgebraicModel.localTranslationDifference_zeroForm (a : F.periodData.space)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).f.hom.app
        (op (M.localPeriodDomain p ⊓ M.localPeriodDomain r)) (M.localTranslationDifference a p r) =
      DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict inf_le_right (M.localTranslationZeroForm a r) -
        DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict inf_le_left (M.localTranslationZeroForm a p) := by
  apply Subtype.ext
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro q
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  let ev := DolbeaultTransition.dbarZeroFormEvaluation (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (M.localPeriodDomain p ⊓ M.localPeriodDomain r) q
  have hs := map_sub ev
    (DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict inf_le_right (M.localTranslationZeroForm a r))
    (DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict inf_le_left (M.localTranslationZeroForm a p))
  have hl := DivisorClass.Chern.Holomorphic.ManifoldZeroForms.holomorphicManifoldZeroForm_apply (M.localTranslationDifference a p r) q 0
  refine hl.trans ((M.localTranslationDifference_value a p r q).trans ?_)
  refine Eq.trans ?_ hs.symm
  exact congrArg₂ (· - ·)
    (M.localTranslationZeroForm_value a r ⟨q.val, q.property.2⟩ 0).symm
    (M.localTranslationZeroForm_value a p ⟨q.val, q.property.1⟩ 0).symm

def AlgebraicModel.ReferenceAlgebraicModel.translationPrimitiveSystem (a : F.periodData.space) :
    DolbeaultTransition.DolbeaultPrimitiveSystem (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) where
  domain := M.localPeriodDomain
  mem_domain := M.mem_localPeriodDomain
  primitive := M.localTranslationZeroForm a
  difference := M.localTranslationDifference a
  difference_map := M.localTranslationDifference_zeroForm a

def AlgebraicModel.ReferenceAlgebraicModel.translationDbarForm (a : F.periodData.space) :
    RepresentationTheory.Theta.Geometric.DolbeaultBoundary.ClosedDbarOneForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  (M.translationPrimitiveSystem a).closedForm _ _

def AlgebraicModel.ReferenceAlgebraicModel.translationUnitCech (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj M.localPeriodDomain 1 :=
  DolbeaultTransition.dbarTransitionUnitCech _ _ (M.translationDbarForm a) ((M.translationPrimitiveSystem a).liftCover _ _)

theorem AlgebraicModel.ReferenceAlgebraicModel.translationUnitCech_closed (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj M.localPeriodDomain 1 (M.translationUnitCech a) = 0 :=
  DolbeaultTransition.dbarTransitionUnitCech_closed _ _ (M.translationDbarForm a) ((M.translationPrimitiveSystem a).liftCover _ _)

theorem AlgebraicModel.ReferenceAlgebraicModel.translationUnitCech_value (a : F.periodData.space)
    (b : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b) :
    (Holomorphic.LogUnitClass.holomorphicUnitSection (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b) (M.translationUnitCech a b)).val q =
        Complex.exp (M.localTranslationDifference a (b 0) (b 1)
          ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property,
            AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩) := by
  have h := DolbeaultTransition.dbarTransitionUnitCech_value _ _ (M.translationDbarForm a)
    ((M.translationPrimitiveSystem a).liftCover _ _) b q
  change _ = Complex.exp ((M.localTranslationZeroForm a (b 1)).val
    ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩ 0 -
      (M.localTranslationZeroForm a (b 0)).val
        ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property⟩ 0) at h
  have hs := congrArg₂ (· - ·)
    (M.localTranslationZeroForm_value a (b 1)
      ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩ 0)
    (M.localTranslationZeroForm_value a (b 0)
      ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property⟩ 0)
  exact h.trans ((congrArg Complex.exp hs).trans (congrArg Complex.exp (M.localTranslationDifference_value a (b 0) (b 1)
    ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property,
      AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩).symm))

theorem AlgebraicModel.ReferenceAlgebraicModel.translationUnitCech_class (a : F.periodData.space) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) M.localPeriodDomain
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
      ((M.translationPrimitiveSystem a).liftCover _ _).iSup_domain 0
      (M.translationUnitCech a) (M.translationUnitCech_closed a) =
        RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
          (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass _ _ (M.translationDbarForm a)) :=
  DolbeaultTransition.dbarTransitionUnitCech_class _ _ (M.translationDbarForm a) ((M.translationPrimitiveSystem a).liftCover _ _)

end

section

/-! The constructed global Dolbeault class has the original reference
theta translation factors on every actual overlap of period charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.translationClass_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.translationClass_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem AlgebraicModel.ReferenceAlgebraicModel.translationDbarForm_restrict (a : F.periodData.space)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (M.localPeriodDomain p) 0 (M.localTranslationZeroForm a p) =
      DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict le_top (M.translationDbarForm a).val :=
  (M.translationPrimitiveSystem a).closedForm_restrict _ _ p

theorem AlgebraicModel.ReferenceAlgebraicModel.translationUnitCech_thetaFactor (a : F.periodData.space)
    (b : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b) :
    (Holomorphic.LogUnitClass.holomorphicUnitSection (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b) (M.translationUnitCech a b)).val q =
      let q' : ↥(M.localPeriodDomain (b 0) ⊓ M.localPeriodDomain (b 1)) :=
        ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property,
          AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩
      (F.polarizationFactor hP).value (M.localPeriodDifference (b 0) (b 1) q') (M.localPeriodLift (b 0) q.val + a) /
        (F.polarizationFactor hP).value (M.localPeriodDifference (b 0) (b 1) q') (M.localPeriodLift (b 0) q.val) :=
  (M.translationUnitCech_value a b q).trans (M.localTranslationDifference_exp a (b 0) (b 1)
    ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property,
      AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩)

def AlgebraicModel.ReferenceAlgebraicModel.translationHolomorphicClass (a : F.periodData.space) :
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 _ _ (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass _ _ (M.translationDbarForm a))

local instance AlgebraicModel.ReferenceAlgebraicModel.translationClass_integralCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.integralSheafCohomologyTwo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))) 2

theorem AlgebraicModel.ReferenceAlgebraicModel.translationHolomorphicClass_zeroChern (a : F.periodData.space) :
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (M.translationHolomorphicClass a) = 0 :=
  RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1_connecting _ _ (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass _ _ (M.translationDbarForm a))

end

/-! Translation coordinates give an actual additive map into the
original holomorphic unit-sheaf cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.translationHom_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.translationHom_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance AlgebraicModel.ReferenceAlgebraicModel.translationHom_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

theorem AlgebraicModel.ReferenceAlgebraicModel.localTranslationDifference_sub (a c : F.periodData.space)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    M.localTranslationDifference (a - c) p r q =
      M.localTranslationDifference a p r q - M.localTranslationDifference c p r q := by
  change (Real.pi : ℂ) * F.form (M.localPeriodDifference p r q).val (a - c) =
    (Real.pi : ℂ) * F.form (M.localPeriodDifference p r q).val a -
      (Real.pi : ℂ) * F.form (M.localPeriodDifference p r q).val c
  exact (congrArg (fun t : ℂ => (Real.pi : ℂ) * t)
    (map_sub (F.form (M.localPeriodDifference p r q).val) a c)).trans (mul_sub _ _ _)

theorem AlgebraicModel.ReferenceAlgebraicModel.translationUnitCech_sub (a c : F.periodData.space) :
    M.translationUnitCech (a - c) = M.translationUnitCech a - M.translationUnitCech c := by
  funext b
  apply Holomorphic.GlobalGluing.holomorphicUnitSection_ext (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b)
  intro q
  let q' : ↥(M.localPeriodDomain (b 0) ⊓ M.localPeriodDomain (b 1)) :=
    ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property,
      AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩
  have hs := Holomorphic.LogUnitClass.holomorphicUnitSection_value_sub (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b) (M.translationUnitCech a b) (M.translationUnitCech c b) q
  exact (M.translationUnitCech_value (a - c) b q).trans
    ((congrArg Complex.exp (M.localTranslationDifference_sub a c (b 0) (b 1) q')).trans
      ((Complex.exp_sub _ _).trans ((congrArg₂ (· / ·)
        (M.translationUnitCech_value a b q).symm (M.translationUnitCech_value c b q).symm).trans hs.symm)))

theorem AlgebraicModel.ReferenceAlgebraicModel.translationHolomorphicClass_sub (a c : F.periodData.space) :
    M.translationHolomorphicClass (a - c) = M.translationHolomorphicClass a - M.translationHolomorphicClass c := by
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let G := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let : AddCommGroup (CategoryTheory.Sheaf.H G 1) := Cech.Add.cechClassAddCommGroup (X := T) G 1
  have hU := ((M.translationPrimitiveSystem (a - c)).liftCover _ _).iSup_domain
  have hs := Cech.Add.cechSub_closed (X := T) M.localPeriodDomain G.obj 1
    (M.translationUnitCech a) (M.translationUnitCech c) (M.translationUnitCech_closed a) (M.translationUnitCech_closed c)
  have he := Cech.Add.cechSheafClass_congr (X := T) M.localPeriodDomain G hU 0
    (M.translationUnitCech (a - c)) (M.translationUnitCech a - M.translationUnitCech c)
    (M.translationUnitCech_closed (a - c)) hs (M.translationUnitCech_sub a c)
  have ha := Cech.Add.cechSheafClass_sub (X := T) M.localPeriodDomain G hU 0
    (M.translationUnitCech a) (M.translationUnitCech c) (M.translationUnitCech_closed a) (M.translationUnitCech_closed c)
  exact (M.translationUnitCech_class (a - c)).symm.trans
    (he.trans (ha.trans (congrArg₂ (· - ·) (M.translationUnitCech_class a) (M.translationUnitCech_class c))))

def AlgebraicModel.ReferenceAlgebraicModel.translationHolomorphicHom : F.periodData.space →+
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) where
  toFun := M.translationHolomorphicClass
  map_zero' := by
    have h := M.translationHolomorphicClass_sub 0 0
    simpa only [sub_self] using h
  map_add' a c := by
    have h := M.translationHolomorphicClass_sub (a + c) c
    rw [add_sub_cancel_right] at h
    exact sub_eq_iff_eq_add.mp h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
