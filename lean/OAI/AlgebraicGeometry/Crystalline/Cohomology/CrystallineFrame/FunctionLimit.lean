import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerDiagram
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Adjunction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators

/-! # Function Limit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FunctionLimit.CrystallineFrameFunctionLimit

noncomputable section

/-!
# The completed envelope is the limit of native frame functions

The native frame functor is right adjoint to forgetting coordinates,
so its opposite preserves computation of limits. The final p-power
tower then identifies the original native frame-function limit with
the original completed PD envelope, in the small Witt-module category.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

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

local instance frameFinal : (G).Final :=
  Functor.final_of_adjunction (Adjunction.CrystallineFrameAdjunction.adjunction p k B σ a)

abbrev framedLimits : HasLimitsOfShape Framedᵒᵖ (ModuleCat.{u} W) :=
  Functor.Initial.hasLimitsOfShape_of_initial (Tower).op

include hr hbase in
theorem hasLimitFunctions : HasLimit F := by
  let : HasLimitsOfShape Framedᵒᵖ (ModuleCat.{u} W) := framedLimits p k B σ r hr hbase
  exact inferInstanceAs (HasLimit ((G).op ⋙ P))

def functionLimit : LimitCone F := by
  let : HasLimit F := hasLimitFunctions p k B σ r hr hbase
  exact getLimitCone F

def functionsLimitIso : (functionLimit p k B σ r hr hbase).cone.pt ≅
    ModuleCat.of W (PD.InverseLimit.PDInverseLimit.Ring p k B EnvelopeTower) := by
  let : HasLimitsOfShape Framedᵒᵖ (ModuleCat.{u} W) := framedLimits p k B σ r hr hbase
  let : HasLimit F := hasLimitFunctions p k B σ r hr hbase
  exact Functor.Initial.limitIso (G).op P ≪≫
    (Functor.Initial.limitIso (Tower).op P).symm ≪≫
      FramedPolynomial.TowerDiagram.FramedPolynomialTowerDiagram.limitIso p k B σ r hr hbase

def completedCone : Cone F where
  pt := ModuleCat.of W (PD.InverseLimit.PDInverseLimit.Ring p k B EnvelopeTower)
  π :=
    { app Q := (functionsLimitIso p k B σ r hr hbase).inv ≫
        (functionLimit p k B σ r hr hbase).cone.π.app Q
      naturality := by
        intro Q S f
        change 𝟙 _ ≫ ((functionsLimitIso p k B σ r hr hbase).inv ≫
          (functionLimit p k B σ r hr hbase).cone.π.app S) =
            ((functionsLimitIso p k B σ r hr hbase).inv ≫
              (functionLimit p k B σ r hr hbase).cone.π.app Q) ≫ (F).map f
        rw [Category.id_comp, Category.assoc, (functionLimit p k B σ r hr hbase).cone.w f] }

def completedConeIsLimit : IsLimit (completedCone p k B σ r hr hbase) :=
  IsLimit.ofIsoLimit (functionLimit p k B σ r hr hbase).isLimit
    (Cone.ext (functionsLimitIso p k B σ r hr hbase) (by
      intro Q
      simp only [completedCone, Iso.hom_inv_id_assoc]))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.FunctionLimit.CrystallineFrameFunctionLimit
