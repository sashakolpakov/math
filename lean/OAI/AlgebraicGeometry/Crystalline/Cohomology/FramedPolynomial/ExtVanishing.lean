import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.DerivedVanishing
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafGlobal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactAdjunction

/-! # Ext Vanishing -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.ExtVanishing.FramedPolynomialExtVanishing

noncomputable section

/-!
# Positive Ext vanishing for the actual framed structure sheaf

The checked global-section complex of the restricted native injective
resolution is exact in positive degrees. Its rank-one sheaf Hom complex
therefore proves vanishing of the actual Ext groups on the framed site.
The exact native frame adjunction transports this to its native image.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "O" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.structureSheaf p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ (fun i => r (MvPolynomial.X i))
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ (fun i => r (MvPolynomial.X i))
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.ExactAdjunction.FramedCrystallineExactAdjunction.restriction p k B σ (fun i => r (MvPolynomial.X i))
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.ExactAdjunction.FramedCrystallineExactAdjunction.frame p k B σ (fun i => r (MvPolynomial.X i))
local notation "CO" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedSections.FramedCrystallineDerivedSections.coefficientSheaf p k B σ (fun i => r (MvPolynomial.X i))
local notation "FO" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.StructureSections.FramedPolynomialStructureSections.structureSheaf p k B σ r

local instance : HasLimitsOfShape Cᵒᵖ V := ModuleCat.hasLimitsOfShape
local instance framedHasExt : HasExt.{u + 2} (Sheaf K V) := HasExt.standard _

include hr hbase in
theorem framed (n : ℕ) (α : Abelian.Ext CO FO (n + 1)) : α = 0 := by
  let I : InjectiveResolution O := injectiveResolution O
  let I' : InjectiveResolution FO := ExactInjective.ExactInjectiveResolution.map U I
  exact SheafGlobal.SheafGlobalExtVanishing.ext_eq_zero K (Site.CoefficientRing p k) FO I' n
    (DerivedVanishing.FramedPolynomialDerivedVanishing.exactAt p k B σ r hr hbase I n) α

include hr hbase in
theorem nativeFrame (n : ℕ)
    (α : Abelian.Ext (Site.coefficientSheaf p k X) ((G).obj FO) (n + 1)) : α = 0 := by
  let I : InjectiveResolution FO := injectiveResolution FO
  apply ExactAdjunction.ExactAdjunctionExtVanishing.rightAdjoint
    (FramedCrystalline.Topology.FramedCrystallineTopology.sheafAdjunction p k B σ (fun i => r (MvPolynomial.X i)) V J) I n _ α
  intro β
  exact ExactAdjunction.ExactAdjunctionExtVanishing.of_sourceIso
    (FramedCrystalline.DerivedSections.FramedCrystallineDerivedSections.coefficientIso p k B σ (fun i => r (MvPolynomial.X i)))
      (n + 1) (framed p k B σ r hr hbase n) β

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.ExtVanishing.FramedPolynomialExtVanishing
