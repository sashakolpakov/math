import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RationalGeometricField
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models

/-! # Points Geometric Point Lift -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsGeometricPointLift.Construction

noncomputable section

/-!
Lift a fixed F_q-bar point of the actual CMPoints special fiber into its
geometric fiber. The algebraic closure of the residue field at the
lifted point is identified with F_q-bar, retaining the original
map into the integral universal-family base.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [NumberField.IsCMField E] [Field K] [NumberField K]
variable (M : PELModuli.CMPoints.Models.RankThreePELModel E K) {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
variable (R : M.GoodIntegralReduction q j) (a : M.Family)

theorem l45GeometricBase_factor : (ModuliPoint.Construction.geometricBase q).hom ≫ R.specialBase = R.geometricBase := by
  change Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (ModuliPoint.Construction.residueClosure q))) ≫
    Spec.map (CommRingCat.ofHom R.residue) = _
  rw [← Spec.map_comp]
  rfl

variable (x : ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a)

def l45GeometricPointIntegralMap : Spec (.of (ModuliPoint.Construction.residueClosure q)) ⟶ (M.integral a).toOver.left :=
  x.left ≫ pullback.fst (M.integral a).toOver.hom R.specialBase

theorem l45GeometricPointIntegralMap_base :
    l45GeometricPointIntegralMap M R a x ≫ (M.integral a).toOver.hom = R.geometricBase := by
  let t : (R.specialFiber a).left ⟶ (M.integral a).toOver.left :=
    pullback.fst (M.integral a).toOver.hom R.specialBase
  have ht : t ≫ (M.integral a).toOver.hom = (R.specialFiber a).hom ≫ R.specialBase :=
    pullback.condition
  exact (Category.assoc x.left t (M.integral a).toOver.hom).trans
    ((congrArg (fun z => x.left ≫ z) ht).trans
      ((Category.assoc x.left (R.specialFiber a).hom R.specialBase).symm.trans
        ((congrArg (fun z => z ≫ R.specialBase) x.w).trans (l45GeometricBase_factor M R))))

/-- The geometric-fiber lift is the actual pullback lift of the
original geometric point, with its original integral projection. -/
def l45GeometricPointLift : Spec (.of (ModuliPoint.Construction.residueClosure q)) ⟶ R.geom a :=
  pullback.lift (l45GeometricPointIntegralMap M R a x) (𝟙 _)
    ((l45GeometricPointIntegralMap_base M R a x).trans (Category.id_comp _).symm)

theorem l45GeometricPointLift_section :
    l45GeometricPointLift M R a x ≫ (R.geometricFiber a).hom = 𝟙 _ :=
  pullback.lift_snd _ _ _

theorem l45GeometricPointLift_projection :
    l45GeometricPointLift M R a x ≫ R.projection a = l45GeometricPointIntegralMap M R a x :=
  pullback.lift_fst _ _ _

def l45GeometricPointIndex : R.geom a :=
  l45GeometricPointLift M R a x (IsLocalRing.closedPoint (ModuliPoint.Construction.residueClosure q))

/-- Compare exactly the geometric residue field used in CMPoints with
the fixed field used in FrobeniusKernel's native geometric point. -/
def l45GeometricPointFieldIso :
    CommRingCat.of (R.fiberField a (l45GeometricPointIndex M R a x)) ≅
      CommRingCat.of (ModuliPoint.Construction.residueClosure q) :=
  RationalGeometricField.Construction.rationalGeometricFieldIso (ModuliPoint.Construction.residueClosure q) (R.geometricFiber a).hom
    (l45GeometricPointLift M R a x) (l45GeometricPointLift_section M R a x)

theorem l45GeometricPointFieldIso_fiberMap :
    Spec.map (l45GeometricPointFieldIso M R a x).hom ≫
      R.fiberMap a (l45GeometricPointIndex M R a x) = l45GeometricPointLift M R a x :=
  RationalGeometricField.Construction.rationalGeometricFieldIso_factor (ModuliPoint.Construction.residueClosure q) (R.geometricFiber a).hom
    (l45GeometricPointLift M R a x) (l45GeometricPointLift_section M R a x)

/-- The field comparison retains the original integral point at
which the universal polarized and marked family is evaluated. -/
theorem l45GeometricPointFieldIso_integral :
    Spec.map (l45GeometricPointFieldIso M R a x).hom ≫
      R.fiberMap a (l45GeometricPointIndex M R a x) ≫ R.projection a =
        l45GeometricPointIntegralMap M R a x := by
  rw [← Category.assoc, l45GeometricPointFieldIso_fiberMap, l45GeometricPointLift_projection]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsGeometricPointLift.Construction
