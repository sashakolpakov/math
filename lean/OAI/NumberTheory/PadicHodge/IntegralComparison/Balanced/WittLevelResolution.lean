import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SmoothProperWittCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionFunctorNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittResolutionLevelCohomology

/-! # Witt Level Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittLevelResolution

noncomputable section

/-! Genuine bounded-level restriction commutes with the balanced
source-resolution comparison on original crystalline Ext. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n m hnm
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition.constantUnitIso (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n m hnm
local notation "Ym" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f m

local instance separated : IsSeparated f := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

omit [Fintype k] [IsProper X.hom] [Smooth X.hom] in
theorem extMap (i : ℕ) :
    ResolutionHom.TransportCohomology.extMap T R (e).inv (𝟙 ((T).obj Ym)) i =
      ModuleCat.ofHom (Bounded.CohomologyTransition.map f n m hnm i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Abelian.Ext.comp_assoc_of_third_deg_zero (Abelian.Ext.mk₀ (e).inv)
    (x.mapExactFunctor T) (Abelian.Ext.mk₀ (𝟙 ((T).obj Ym))) (zero_add i)).symm

theorem homology (i : ℕ) : HomologicalComplex.homologyMap
    (SmoothProper.WittResolutionLevelCohomology.map p k X n m hnm) i ≫
      (SmoothProperWittCup.resolutionHomologyIso p k X n i).hom =
        (SmoothProperWittCup.resolutionHomologyIso p k X m i).hom ≫
          ModuleCat.ofHom (Bounded.CohomologyTransition.map f n m hnm i) := by
  let : QuasiIso (SmoothProper.WittPresentationResolution.augmentation p k X n) :=
    SmoothProper.WittPresentationResolution.augmentation_quasiIso p k X n
  let : QuasiIso (SmoothProper.WittPresentationResolution.augmentation p k X m) :=
    SmoothProper.WittPresentationResolution.augmentation_quasiIso p k X m
  have H := ResolutionFunctorNaturality.homology T R Ym
    (SmoothProper.WittPresentationResolution.complex p k X m)
    (SmoothProper.WittPresentationResolution.complex p k X n)
    (SmoothProper.WittResolutionReduction.map p k X n m hnm)
    (SmoothProper.WittPresentationResolution.augmentation p k X m)
    (SmoothProper.WittPresentationResolution.augmentation p k X n) (e).inv
    (SmoothProper.WittResolutionReduction.augmentation_zero p k X n m hnm)
    (BalancedBounded.CechCup.resolution p k f m)
    (BalancedBounded.CechCup.resolution p k f n)
    (BoundedFrame.ResolutionAcyclicity.subsingleton p k f m (SmoothProper.WittFrameFamily.Family.frame p k X m))
    (BoundedFrame.ResolutionAcyclicity.subsingleton p k f n (SmoothProper.WittFrameFamily.Family.frame p k X n)) i
  exact H.trans (congrArg
    (fun a => (SmoothProperWittCup.resolutionHomologyIso p k X m i).hom ≫ a)
    (extMap p k X n m hnm i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittLevelResolution
