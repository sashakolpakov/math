import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FunctionLimit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.EvaluationDerivative

/-! # Limit Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.LimitEvaluation.CrystallineFrameLimitEvaluation

noncomputable section

/-!
# The frame-function limit evaluates by the actual PD maps

The categorical limit identification restricts on each p-power level
to its original quotient coordinate. On a native free frame, it is
therefore evaluation along the actual coordinate-preserving PD map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "Poly" => MvPolynomial σ W
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "Framed" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower.FramedPolynomialTower.tower p k B σ r hr hbase
local notation "EnvelopeTower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase
local notation "P" => Functor.op U ⋙ OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.functions p k X
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a
local notation "Completed" => ModuleCat.of W (OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B EnvelopeTower)

local instance frameFinal : (G).Final :=
  Functor.final_of_adjunction (Adjunction.CrystallineFrameAdjunction.adjunction p k B σ a)

def framedLimit : LimitCone P := by
  let : HasLimitsOfShape Framedᵒᵖ (ModuleCat.{u} W) :=
    FunctionLimit.CrystallineFrameFunctionLimit.framedLimits p k B σ r hr hbase
  exact getLimitCone P

def framedIso : (framedLimit p k B σ r hr hbase).cone.pt ≅ Completed := by
  let : HasLimitsOfShape Framedᵒᵖ (ModuleCat.{u} W) :=
    FunctionLimit.CrystallineFrameFunctionLimit.framedLimits p k B σ r hr hbase
  exact (Functor.Initial.limitIso (Tower).op P).symm ≪≫
    FramedPolynomial.TowerDiagram.FramedPolynomialTowerDiagram.limitIso p k B σ r hr hbase

def framedCone : Cone P where
  pt := Completed
  π :=
    { app Q := (framedIso p k B σ r hr hbase).inv ≫ (framedLimit p k B σ r hr hbase).cone.π.app Q
      naturality := by
        intro Q S f
        change 𝟙 _ ≫ ((framedIso p k B σ r hr hbase).inv ≫
          (framedLimit p k B σ r hr hbase).cone.π.app S) =
            ((framedIso p k B σ r hr hbase).inv ≫
              (framedLimit p k B σ r hr hbase).cone.π.app Q) ≫ (P).map f
        rw [Category.id_comp, Category.assoc, (framedLimit p k B σ r hr hbase).cone.w f] }

theorem nativeProjection (Q : Site.Object p k X) :
    (FunctionLimit.CrystallineFrameFunctionLimit.completedCone p k B σ r hr hbase).π.app (op Q) =
      (framedCone p k B σ r hr hbase).π.app (op ((G).obj Q)) := by
  let : HasLimitsOfShape Framedᵒᵖ (ModuleCat.{u} W) :=
    FunctionLimit.CrystallineFrameFunctionLimit.framedLimits p k B σ r hr hbase
  let : HasLimit F := FunctionLimit.CrystallineFrameFunctionLimit.hasLimitFunctions p k B σ r hr hbase
  let e : limit P ≅ Completed := (Functor.Initial.limitIso (Tower).op P).symm ≪≫
    FramedPolynomial.TowerDiagram.FramedPolynomialTowerDiagram.limitIso p k B σ r hr hbase
  change (e.inv ≫ limit.pre P (G).op) ≫
    limit.π ((G).op ⋙ P) (op Q) = e.inv ≫
      limit.π P (op ((G).obj Q))
  rw [Category.assoc, limit.pre_π]
  rfl

theorem towerProjection (n : ℕ) :
    (framedCone p k B σ r hr hbase).π.app (op ((Tower).obj n)) =
      ModuleCat.ofHom (PD.InverseLimit.PDInverseLimit.eval p k B EnvelopeTower n).toLinearMap := by
  let : HasLimitsOfShape Framedᵒᵖ (ModuleCat.{u} W) :=
    FunctionLimit.CrystallineFrameFunctionLimit.framedLimits p k B σ r hr hbase
  let e := Functor.Initial.limitIso (Tower).op P
  have hp : e.hom ≫ limit.π P (op ((Tower).obj n)) = limit.π ((Tower).op ⋙ P) (op n) := by
    have hpre := limit.pre_π P (Tower).op (op n)
    change e.inv ≫ limit.π ((Tower).op ⋙ P) (op n) = limit.π P (op ((Tower).obj n)) at hpre
    exact (congrArg (fun f => e.hom ≫ f) hpre).symm.trans (e.hom_inv_id_assoc _)
  let ed : limit ((Tower).op ⋙ P) ≅ Completed :=
    FramedPolynomial.TowerDiagram.FramedPolynomialTowerDiagram.limitIso p k B σ r hr hbase
  change (ed.inv ≫ e.hom) ≫
    limit.π P (op ((Tower).obj n)) = _
  rw [Category.assoc, hp]
  change ((PD.InverseLimitUniversal.PDInverseLimitUniversal.limitIso p k B EnvelopeTower).hom ≫
    (HasLimit.isoOfNatIso (FramedPolynomial.TowerDiagram.FramedPolynomialTowerDiagram.diagramIso p k B σ r hr hbase)).inv) ≫
      limit.π (FramedPolynomial.TowerDiagram.FramedPolynomialTowerDiagram.functions p k B σ r hr hbase) (op n) = _
  rw [Category.assoc, HasLimit.isoOfNatIso_inv_π]
  change (PD.InverseLimitUniversal.PDInverseLimitUniversal.limitIso p k B EnvelopeTower).hom ≫
    limit.π (EnvelopeTower ⋙ PD.InverseLimitUniversal.PDInverseLimitUniversal.ambientModules p k B) (op n) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (PD.InverseLimitUniversal.PDInverseLimitUniversal.isLimit p k B EnvelopeTower) (limit.isLimit _) (op n)

theorem native_eval (Q : Site.Object p k X) (n : ℕ)
    (hn : (p : ((G).obj Q).base.thickening.ring) ^ (n + 1) = 0)
    (x : PD.InverseLimit.PDInverseLimit.Ring p k B EnvelopeTower) :
    (FunctionLimit.CrystallineFrameFunctionLimit.completedCone p k B σ r hr hbase).π.app (op Q) x =
      EvaluationDerivative.CrystallineFrameEvaluationDerivative.evaluate p k B σ r hr hbase Q n hn
        (PD.InverseLimit.PDInverseLimit.eval p k B EnvelopeTower n x) := by
  rw [nativeProjection]
  let g := FramedPolynomial.Levels.FramedPolynomialLevels.map p k B σ r hr hbase ((G).obj Q) n hn
  have h := (framedCone p k B σ r hr hbase).w g.op
  change (framedCone p k B σ r hr hbase).π.app (op ((Tower).obj n)) ≫ (P).map g.op =
    (framedCone p k B σ r hr hbase).π.app (op ((G).obj Q)) at h
  rw [towerProjection] at h
  exact (ConcreteCategory.congr_hom h x).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.LimitEvaluation.CrystallineFrameLimitEvaluation
