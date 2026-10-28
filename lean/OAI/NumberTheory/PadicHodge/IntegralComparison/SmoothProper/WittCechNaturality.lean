import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittResolutionLevelCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittResolutionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainFunctorCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechTermKernel

/-! # Witt Cech Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechNaturality.Comparison

noncomputable section

/-! The original global source-resolution comparison intertwines actual Witt ring Čech transitions in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family
  WittCechTransitionData

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n m hnm
local notation "Ym" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) m
local notation "σn" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechResolution.Comparison.iso p k X n
local notation "σm" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechResolution.Comparison.iso p k X m

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} R) := by
  let h : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) := ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  exact fun I => h.has_limits_of_shape (Discrete I)

def liftedMap : WittCechCohomology.complex p k X m ⟶ WittCechCohomology.complex p k X n :=
  ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
    (WittCechTransition.map p k X n m hnm)

theorem coefficient (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) :
    (BigCrystallineCohomology.structureSheaf (Witt.Crystalline.wittStructureMap p k X)).obj.map
      (WittTupleReduction.morphism p k X n m hnm a t).op ≫
        (WittCechResolution.Comparison.coefficientIso p k X n).inv.app
          (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t)) =
      (WittCechResolution.Comparison.coefficientIso p k X m).inv.app
        (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X m) a t)) ≫
          WittCechTransitionData.coefficient p k X n m hnm a t :=
  (Crystalline.StructureDescent.structurePresheafIso (Witt.Crystalline.wittStructureMap p k X)).inv.naturality
    (WittTupleReduction.morphism p k X n m hnm a t).op

theorem coordinate (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X)
    (f : (WittPresentationResolution.complex p k X m).X a ⟶ Ym) :
    WittCechTransitionData.coordinate p k X n a t
      (((σn).hom.f a ((WittResolutionLevelCohomology.map p k X n m hnm).f a (Abelian.Ext.mk₀ f))).down) =
        WittCechTransitionData.coordinate p k X n a t
          (((liftedMap p k X n m hnm).f a ((σm).hom.f a (Abelian.Ext.mk₀ f))).down) := by
  let f' := (WittResolutionReduction.map p k X n m hnm).f a ≫ (T).map f
  have hm := Acyclic.ChainFunctorCoordinates.map_mk T R Ym
    (WittPresentationResolution.complex p k X m)
    (WittPresentationResolution.complex p k X n)
    (WittResolutionReduction.map p k X n m hnm) a f
  have hn := WittCechResolution.Comparison.coordinate_mk p k X n a t f'
  have hs := WittResolutionCoordinates.coordinate p k X n m hnm a t f
  have he := congrArg (fun c => c (Presentation.ResolutionCoordinates.sheaf.{u + 1, u}
    (WittFrameFamily.Family.frame p k X m) R a (BoundedCrystalline.Site.topology (Witt.Crystalline.wittStructureMap p k X) m) Ym f t))
      (coefficient p k X n m hnm a t)
  have hl := (congrArg (fun x => WittCechTransitionData.coordinate p k X n a t
    (((σn).hom.f a x).down)) hm).trans
      (hn.trans ((congrArg ((WittCechResolution.Comparison.coefficientIso p k X n).inv.app
        (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t))) hs).trans he))
  have hr := (congrArg (fun c => c (((σm).hom.f a (Abelian.Ext.mk₀ f)).down))
    (WittCechTransitionData.termMap_coordinate p k X n m hnm a t)).trans
      (congrArg (WittCechTransitionData.coefficient p k X n m hnm a t)
        (WittCechResolution.Comparison.coordinate_mk p k X m a t f))
  exact hl.trans hr.symm

theorem complexes : WittResolutionLevelCohomology.map p k X n m hnm ≫ (σn).hom =
    (σm).hom ≫ liftedMap p k X n m hnm := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Abelian.Ext.{u + 2} ((WittPresentationResolution.complex p k X m).X a) Ym 0 at x
  obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
  apply ULift.ext
  apply Module.ProductScalarKernel.element_ext.{u + 1, u, u + 1}
    (WittCoefficientKernel.sectionModule p k X n a)
  intro t
  exact coordinate p k X n m hnm a t f

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechNaturality.Comparison
