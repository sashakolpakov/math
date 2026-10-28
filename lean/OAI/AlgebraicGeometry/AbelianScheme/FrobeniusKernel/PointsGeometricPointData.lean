import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsGeometricPointLift
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Points Geometric Point Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsGeometricPointData.Construction

noncomputable section

/-!
The residue-field point used by CMPoints and the fixed geometric point
carry the same original polarized, marked integral-action family.
The isomorphism is constructed from the actual field factorization
and native pullback coherence, including the Poincare bundle.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [NumberField.IsCMField E] [Field K] [NumberField K]
variable (M : PELModuli.CMPoints.Models.RankThreePELModel E K) {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
variable (R : M.GoodIntegralReduction q j) (a : M.Family)

def l45FiberActionData (y : R.geom a) :
    PELModuli.IntegralModel.PEL.Has.PolarizedActionData E (3 * M.s) (M.datum a).polarizationType (M.level a)
      (Spec (.of (R.fiberField a y))) :=
  (((M.integral a).universal.data).pullback (R.projection a)).pullback (R.fiberMap a y)

theorem l45FiberActionData_polarized (y : R.geom a) :
    (l45FiberActionData M R a y).polarized = R.fiberPolarized a y := rfl

theorem l45FiberActionData_action (y : R.geom a) :
    (l45FiberActionData M R a y).action = R.fiberAction a y := rfl

variable (x : ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a)

def l45FixedPointActionData :
    PELModuli.IntegralModel.PEL.Has.PolarizedActionData E (3 * M.s) (M.datum a).polarizationType (M.level a)
      (Spec (.of (ModuliPoint.Construction.residueClosure q))) :=
  (M.integral a).universal.data.pullback (PointsGeometricPointLift.Construction.l45GeometricPointIntegralMap M R a x)

/-- All the original source data are retained when moving from the
CMPoints geometric residue field to the fixed field of the FrobeniusKernel point. -/
def l45GeometricPointDataIso : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
    ((l45FiberActionData M R a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x)).pullback
      (Spec.map (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom))
    (l45FixedPointActionData M R a x) := by
  let U := (M.integral a).universal.data
  let y := PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x
  let t := Spec.map (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom
  have h : (t ≫ R.fiberMap a y) ≫ R.projection a = PointsGeometricPointLift.Construction.l45GeometricPointIntegralMap M R a x :=
    (Category.assoc _ _ _).trans (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso_integral M R a x)
  change PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
    (((U.pullback (R.projection a)).pullback (R.fiberMap a y)).pullback t)
    (U.pullback (PointsGeometricPointLift.Construction.l45GeometricPointIntegralMap M R a x))
  rw [← h]
  exact (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackComp (U.pullback (R.projection a)) (R.fiberMap a y) t).trans
    (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso.pullbackComp U (R.projection a) (t ≫ R.fiberMap a y))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsGeometricPointData.Construction
