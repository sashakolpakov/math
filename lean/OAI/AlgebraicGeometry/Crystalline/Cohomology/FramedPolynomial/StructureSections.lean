import OAI.AlgebraicGeometry.Crystalline.Cohomology.StructureSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerDiagram

/-! # Structure Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.StructureSections.FramedPolynomialStructureSections

noncomputable section

/-!
# Native framed structure-sheaf sections are the completed PD envelope

The original structure sheaf has its actual ambient modules as sections.
Finality of the native framed tower and the identified quotient transitions
therefore compute its ordinary framed global sections as the existing
ring of compatible p-power PD-envelope residues, with the native lifted
Witt-module coefficients.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "W" => WittVector p k
local notation "A" => MvPolynomial σ W
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ a
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafPushforward.CrystallineFrameSheafPushforward.Coefficients p k
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower.FramedPolynomialTower.tower p k B σ r hr hbase
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B A r hr hbase
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerDiagram.FramedPolynomialTowerDiagram.functions p k B σ r hr hbase
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k

local instance presheafLimits : HasLimitsOfShape Cᵒᵖ V := ModuleCat.hasLimitsOfShape

local instance coefficientLimits : PreservesLimitsOfShape ℕᵒᵖ E := by
  unfold PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift
  have : PreservesLimitsOfSize.{u, u} (ModuleCat.uliftFunctor.{u + 1, u} W) := inferInstance
  have : PreservesLimitsOfSize.{0, 0} (ModuleCat.uliftFunctor.{u + 1, u} W) :=
    preservesSmallestLimits_of_preservesLimits _
  have : PreservesLimitsOfShape ℕᵒᵖ
      (ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv : Site.CoefficientRing p k ≃+* W).toRingHom) :=
    ⟨fun {K'} => ModuleCat.preservesLimit_restrictScalars _ K'⟩
  exact comp_preservesLimitsOfShape _ _

def structureSheaf : Sheaf K V :=
  (FramedCrystalline.ExactAdjunction.FramedCrystallineExactAdjunction.restriction p k B σ a).obj (Site.structureSheaf p k X)

def towerSectionsIso : (T).op ⋙ (structureSheaf p k B σ r).obj ≅ F ⋙ E :=
  Functor.isoWhiskerLeft ((T).op ⋙ (U).op) (StructureSections.CrystallineStructureSections.structurePresheafIso p k X)

def completedModule : V := (E).obj (ModuleCat.of W (PD.InverseLimit.PDInverseLimit.Ring p k B D))

def globalSectionsIso : (Sheaf.Γ K V).obj (structureSheaf p k B σ r) ≅ completedModule p k B σ r hr hbase :=
  TowerSections.FramedPolynomialTowerSections.globalSectionsIso p k B σ r hr hbase (structureSheaf p k B σ r) ≪≫
    HasLimit.isoOfNatIso (towerSectionsIso p k B σ r hr hbase) ≪≫
    (preservesLimitIso E F).symm ≪≫
    (E).mapIso (TowerDiagram.FramedPolynomialTowerDiagram.limitIso p k B σ r hr hbase)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.StructureSections.FramedPolynomialStructureSections
