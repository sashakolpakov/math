import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechPresheafRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.FrameRefinement

/-! # Presheaf Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.PresheafRefinement

noncomputable section

/-! Refinement invariance for the actual ambient-ring presheaf Čech
comparison with original bounded crystalline Ext. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι κ : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (G : κ → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (ρ : ι → κ)
  (α : ∀ i, F i ⟶ G (ρ i))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "P" => Functor.comp (Functor.op (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion f n)) (OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.largePresheaf f)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} R) := by
  let h : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) := ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  exact fun I => h.has_limits_of_shape (Discrete I)

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechPresheafRefinement (liftedMap complexes)

theorem homology
    (hF : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U)
    (hG : ∀ U, CoveringObjectsSheafDetection.sieve G U ∈ BoundedCrystalline.Site.topology f n U) (i : ℕ) :
    HomologicalComplex.homologyMap (BoundedFrame.CechPresheafRefinement.liftedMap p k f n F G ρ α) i ≫
      (CechCup.presheafHomologyIso p k f n F hF i).hom =
        (CechCup.presheafHomologyIso p k f n G hG i).hom := by
  let a := BoundedFrame.CechPresheafRefinement.liftedMap p k f n F G ρ α
  let b := (BoundedFrame.CechPresheafCohomology.sheafIso p k f n F).hom
  let c := (BoundedFrame.CechPresheafCohomology.sheafIso p k f n G).hom
  let d := BoundedFrame.CechRefinement.map p k f n F G ρ α
  let h := (CechCup.sheafHomologyIso p k f n F hF i).hom
  have hs := (HomologicalComplex.homologyMap_comp a b i).symm.trans
    ((congrArg (fun z => HomologicalComplex.homologyMap z i) (BoundedFrame.CechPresheafRefinement.complexes p k f n F G ρ α)).trans
      (HomologicalComplex.homologyMap_comp c d i))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ h) hs).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => HomologicalComplex.homologyMap c i ≫ z)
          (FrameRefinement.homology p k f n F G ρ α hF hG i))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.PresheafRefinement
