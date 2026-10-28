import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameGlobalAcyclic
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafAugmentation

/-! # Intrinsic Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSections.BigCrystallineIntrinsicSections

noncomputable section

/-! # The actual big and native frame-section complexes are isomorphic -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Fintype σ] (a : σ → B)

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX
local notation "A'" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.coefficientSheaf p k X
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.restriction p k B
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a

def map : NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R A K ⟶ NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R A' L :=
  Acyclic.TransportNaturality.AcyclicTransportNaturality.sectionMap R F A (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.constantIso p k B).inv
    (IntrinsicSheafResolution.BigCrystallineIntrinsicSheafResolution.iso p k B σ a).hom

theorem component (j : ℕ) (α : Ext.{u + 2} A ((K).X j) 0) :
    ((map p k B σ a).f j).hom α = FrameGlobalAcyclic.BigCrystallineFrameGlobalAcyclic.termEquiv p k B σ a j 0 α := by
  change (Ext.mk₀ (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.constantIso p k B).inv).comp
      ((α.mapExactFunctor F).comp (Ext.mk₀ (FrameGlobalAcyclic.BigCrystallineFrameGlobalAcyclic.termIso p k B σ a j).hom) (add_zero 0))
      (zero_add 0) =
    ((Ext.mk₀ (IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.constantIso p k B).inv).comp
      (α.mapExactFunctor F) (zero_add 0)).comp
        (Ext.mk₀ (FrameGlobalAcyclic.BigCrystallineFrameGlobalAcyclic.termIso p k B σ a j).hom) (add_zero 0)
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add 0)).symm

instance map_isIso : IsIso (map p k B σ a) := by
  have hc : ∀ j, IsIso ((map p k B σ a).f j) := by
    intro j
    let e : (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R A K).X j ≅
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R A' L).X j :=
      (FrameGlobalAcyclic.BigCrystallineFrameGlobalAcyclic.termEquiv p k B σ a j 0).toModuleIso
    have he : (map p k B σ a).f j = e.hom := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro α
      exact component p k B σ a j α
    exact he.symm ▸ (inferInstance : IsIso e.hom)
  let := hc
  exact HomologicalComplex.Hom.isIso_of_components _

def iso : NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R A K ≅ NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R A' L :=
  asIso (map p k B σ a)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSections.BigCrystallineIntrinsicSections
