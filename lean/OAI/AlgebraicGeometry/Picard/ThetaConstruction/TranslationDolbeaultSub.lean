import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodLiftDisplacements
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultTransition

/-! # Translation Dolbeault Sub -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

section

/-! The ThetaConstruction translation potentials glue through the actual
Dolbeault sequence and give a holomorphic unit class with precisely the
original theta translation factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultTransition

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationDolbeault_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationDolbeault_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.localTranslationDifference_zeroForm (a : DefinitionsIntegral.Tangent g)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    (RepresentationTheory.Theta.Geometric.DolbeaultClosedSequence.holomorphicDbarClosedSequence (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).f.hom.app
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
  let ev := AbelianModuli.ReferenceFamily.DolbeaultTransition.dbarZeroFormEvaluation (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
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

def PeriodModel.Geometric.AlgebraicPeriodModel.translationPrimitiveSystem (a : DefinitionsIntegral.Tangent g) :
    AbelianModuli.ReferenceFamily.DolbeaultTransition.DolbeaultPrimitiveSystem (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) where
  domain := M.localPeriodDomain
  mem_domain := M.mem_localPeriodDomain
  primitive := M.localTranslationZeroForm a
  difference := M.localTranslationDifference a
  difference_map := M.localTranslationDifference_zeroForm a

def PeriodModel.Geometric.AlgebraicPeriodModel.translationDbarForm (a : DefinitionsIntegral.Tangent g) :
    RepresentationTheory.Theta.Geometric.DolbeaultBoundary.ClosedDbarOneForm (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  (M.translationPrimitiveSystem a).closedForm _ _

def PeriodModel.Geometric.AlgebraicPeriodModel.translationUnitCech (a : DefinitionsIntegral.Tangent g) :
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj M.localPeriodDomain 1 :=
  AbelianModuli.ReferenceFamily.DolbeaultTransition.dbarTransitionUnitCech _ _ (M.translationDbarForm a) ((M.translationPrimitiveSystem a).liftCover _ _)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationUnitCech_closed (a : DefinitionsIntegral.Tangent g) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).obj M.localPeriodDomain 1 (M.translationUnitCech a) = 0 :=
  AbelianModuli.ReferenceFamily.DolbeaultTransition.dbarTransitionUnitCech_closed _ _ (M.translationDbarForm a) ((M.translationPrimitiveSystem a).liftCover _ _)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationUnitCech_value (a : DefinitionsIntegral.Tangent g)
    (b : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b) :
    (AbelianModuli.ReferenceFamily.Holomorphic.LogUnitClass.holomorphicUnitSection (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b) (M.translationUnitCech a b)).val q =
        Complex.exp (M.localTranslationDifference a (b 0) (b 1)
          ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property,
            AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩) := by
  have h := AbelianModuli.ReferenceFamily.DolbeaultTransition.dbarTransitionUnitCech_value _ _ (M.translationDbarForm a)
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

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationUnitCech_class (a : DefinitionsIntegral.Tangent g) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) M.localPeriodDomain
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
      ((M.translationPrimitiveSystem a).liftCover _ _).iSup_domain 0
      (M.translationUnitCech a) (M.translationUnitCech_closed a) =
        RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
          (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass _ _ (M.translationDbarForm a)) :=
  AbelianModuli.ReferenceFamily.DolbeaultTransition.dbarTransitionUnitCech_class _ _ (M.translationDbarForm a) ((M.translationPrimitiveSystem a).liftCover _ _)

end

section

/-! The constructed global Dolbeault class has the original primitive
theta translation factors on every actual overlap of period charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultTransition

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationClass_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationClass_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationDbarForm_restrict (a : DefinitionsIntegral.Tangent g)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    DivisorClass.Chern.Manifold.DolbeaultCharts.pureOpenManifoldDolbeaultD (M.localPeriodDomain p) 0 (M.localTranslationZeroForm a p) =
      DivisorClass.Chern.Open.ManifoldBidegree.antiOpenManifoldFormRestrict le_top (M.translationDbarForm a).val :=
  (M.translationPrimitiveSystem a).closedForm_restrict _ _ p

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationUnitCech_thetaFactor (hE : E.transpose = -E) (a : (ProjectivePeriodData.Geometric.projectivePeriodData T).space)
    (b : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b) :
    (AbelianModuli.ReferenceFamily.Holomorphic.LogUnitClass.holomorphicUnitSection (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b) (M.translationUnitCech a b)).val q =
      let q' : ↥(M.localPeriodDomain (b 0) ⊓ M.localPeriodDomain (b 1)) :=
        ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property,
          AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩
      (PolarizationFactor.Geometric.polarizationFactor T hE).value (M.localPeriodDifference (b 0) (b 1) q') (M.localPeriodLift (b 0) q.val + a) /
        (PolarizationFactor.Geometric.polarizationFactor T hE).value (M.localPeriodDifference (b 0) (b 1) q') (M.localPeriodLift (b 0) q.val) :=
  (M.translationUnitCech_value a b q).trans (M.localTranslationDifference_exp hE a (b 0) (b 1)
    ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property,
      AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩)

def PeriodModel.Geometric.AlgebraicPeriodModel.translationHolomorphicClass (a : DefinitionsIntegral.Tangent g) :
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 _ _ (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass _ _ (M.translationDbarForm a))

local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationClass_integralCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.integralSheafCohomologyTwo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))) 2

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationHolomorphicClass_zeroChern (a : DefinitionsIntegral.Tangent g) :
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (M.translationHolomorphicClass a) = 0 :=
  RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1_connecting _ _ (RepresentationTheory.Theta.Geometric.DolbeaultBoundary.holomorphicDbarClass _ _ (M.translationDbarForm a))

end

/-! Translation coordinates give an actual additive map into the
original holomorphic unit-sheaf cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DolbeaultTransition

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationHom_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationHom_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationHom_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

theorem PeriodModel.Geometric.AlgebraicPeriodModel.localTranslationDifference_sub (a c : DefinitionsIntegral.Tangent dim)
    (p r : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (q : ↥(M.localPeriodDomain p ⊓ M.localPeriodDomain r)) :
    M.localTranslationDifference (a - c) p r q =
      M.localTranslationDifference a p r q - M.localTranslationDifference c p r q := by
  change (Real.pi : ℂ) * T.riemannForm (M.localPeriodDifference p r q).val (a - c) =
    (Real.pi : ℂ) * T.riemannForm (M.localPeriodDifference p r q).val a -
      (Real.pi : ℂ) * T.riemannForm (M.localPeriodDifference p r q).val c
  exact (congrArg (fun t : ℂ => (Real.pi : ℂ) * t)
    (map_sub (T.riemannForm (M.localPeriodDifference p r q).val) a c)).trans (mul_sub _ _ _)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationUnitCech_sub (a c : DefinitionsIntegral.Tangent dim) :
    M.translationUnitCech (a - c) = M.translationUnitCech a - M.translationUnitCech c := by
  funext b
  apply AbelianModuli.ReferenceFamily.Holomorphic.GlobalGluing.holomorphicUnitSection_ext (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b)
  intro q
  let q' : ↥(M.localPeriodDomain (b 0) ⊓ M.localPeriodDomain (b 1)) :=
    ⟨q.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 0 q.property,
      AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le M.localPeriodDomain b 1 q.property⟩
  have hs := AbelianModuli.ReferenceFamily.Holomorphic.LogUnitClass.holomorphicUnitSection_value_sub (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection M.localPeriodDomain b) (M.translationUnitCech a b) (M.translationUnitCech c b) q
  exact (M.translationUnitCech_value (a - c) b q).trans
    ((congrArg Complex.exp (M.localTranslationDifference_sub a c (b 0) (b 1) q')).trans
      ((Complex.exp_sub _ _).trans ((congrArg₂ (· / ·)
        (M.translationUnitCech_value a b q).symm (M.translationUnitCech_value c b q).symm).trans hs.symm)))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationHolomorphicClass_sub (a c : DefinitionsIntegral.Tangent dim) :
    M.translationHolomorphicClass (a - c) = M.translationHolomorphicClass a - M.translationHolomorphicClass c := by
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let G := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let : AddCommGroup (CategoryTheory.Sheaf.H G 1) := AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := T) G 1
  have hU := ((M.translationPrimitiveSystem (a - c)).liftCover _ _).iSup_domain
  have hs := AbelianModuli.ReferenceFamily.Cech.Add.cechSub_closed (X := T) M.localPeriodDomain G.obj 1
    (M.translationUnitCech a) (M.translationUnitCech c) (M.translationUnitCech_closed a) (M.translationUnitCech_closed c)
  have he := AbelianModuli.ReferenceFamily.Cech.Add.cechSheafClass_congr (X := T) M.localPeriodDomain G hU 0
    (M.translationUnitCech (a - c)) (M.translationUnitCech a - M.translationUnitCech c)
    (M.translationUnitCech_closed (a - c)) hs (M.translationUnitCech_sub a c)
  have ha := AbelianModuli.ReferenceFamily.Cech.Add.cechSheafClass_sub (X := T) M.localPeriodDomain G hU 0
    (M.translationUnitCech a) (M.translationUnitCech c) (M.translationUnitCech_closed a) (M.translationUnitCech_closed c)
  exact (M.translationUnitCech_class (a - c)).symm.trans
    (he.trans (ha.trans (congrArg₂ (· - ·) (M.translationUnitCech_class a) (M.translationUnitCech_class c))))

def PeriodModel.Geometric.AlgebraicPeriodModel.translationHolomorphicHom : DefinitionsIntegral.Tangent dim →+
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) where
  toFun := M.translationHolomorphicClass
  map_zero' := by
    have h := M.translationHolomorphicClass_sub 0 0
    simpa only [sub_self] using h
  map_add' a c := by
    have h := M.translationHolomorphicClass_sub (a + c) c
    rw [add_sub_cancel_right] at h
    exact sub_eq_iff_eq_add.mp h.symm

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
