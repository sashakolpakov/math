import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittResolutionReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainFunctorNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameCohomology

/-! # Witt Resolution Level Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittResolutionLevelCohomology

noncomputable section

/-! Restriction of the original global Witt source resolution computes exactly the original bounded crystalline Ext transition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n m hnm
local notation "Ym" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) m
local notation "Zm" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) m
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition.constantUnitIso (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n m hnm

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def map : WittFrameCohomology.complex p k X m ⟶ WittFrameCohomology.complex p k X n :=
  Acyclic.ChainFunctorNaturality.map T R Ym
    (WittPresentationResolution.complex p k X m)
    (WittPresentationResolution.complex p k X n)
    (WittResolutionReduction.map p k X n m hnm)

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] in
theorem extMap (i : ℕ) : IntegralComparison.Ext.SourceExactFunctorModule.component T R Ym i (op Zm) ≫
    (IntegralComparison.Ext.ContravariantModuleFunctor.functor R ((T).obj Ym) i).map (e).inv.op =
      ModuleCat.ofHom (Bounded.CohomologyTransition.map (Witt.Crystalline.wittStructureMap p k X) n m hnm i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  exact (Ext.comp_mk₀_id _).symm

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (WittResolutionLevelCohomology.map p k X n m hnm) i ≫
    (WittFrameCohomology.homologyIso p k X n i).hom =
      (WittFrameCohomology.homologyIso p k X m i).hom ≫
        ModuleCat.ofHom (Bounded.CohomologyTransition.map (Witt.Crystalline.wittStructureMap p k X) n m hnm i) := by
  let hn : QuasiIso (WittPresentationResolution.augmentation p k X n) :=
    WittPresentationResolution.augmentation_quasiIso p k X n
  let hm : QuasiIso (WittPresentationResolution.augmentation p k X m) :=
    WittPresentationResolution.augmentation_quasiIso p k X m
  have h := Acyclic.ChainFunctorNaturality.homology T R Ym
    (WittPresentationResolution.complex p k X m)
    (WittPresentationResolution.complex p k X n)
    (WittResolutionReduction.map p k X n m hnm)
    (WittPresentationResolution.augmentation p k X m)
    (WittPresentationResolution.augmentation p k X n) (e).inv
    (WittResolutionReduction.augmentation_zero p k X n m hnm)
    (BoundedFrame.ResolutionAcyclicity.subsingleton p k (Witt.Crystalline.wittStructureMap p k X) m (WittFrameFamily.Family.frame p k X m))
    (BoundedFrame.ResolutionAcyclicity.subsingleton p k (Witt.Crystalline.wittStructureMap p k X) n (WittFrameFamily.Family.frame p k X n))
    (WittResolutionReduction.restricted_acyclic p k X n m hnm) i
  exact h.trans (congrArg (fun a => (WittFrameCohomology.homologyIso p k X m i).hom ≫ a)
    (extMap p k X n m hnm i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittResolutionLevelCohomology
