import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup

/-! # Frame Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.FrameRefinement

noncomputable section

/-! Refining a genuine bounded crystalline cover preserves the canonical
comparison with the original Ext groups in every degree. Both acyclicity
and resolution exactness are discharged by the native geometric results. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι κ : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (G : κ → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (ρ : ι → κ)
  (α : ∀ i, F i ⟶ G (ρ i))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechRefinement (map)

theorem homology
    (hF : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U)
    (hG : ∀ U, CoveringObjectsSheafDetection.sieve G U ∈ BoundedCrystalline.Site.topology f n U) (i : ℕ) :
    HomologicalComplex.homologyMap (BoundedFrame.CechRefinement.map p k f n F G ρ α) i ≫
      (CechCup.sheafHomologyIso p k f n F hF i).hom =
        (CechCup.sheafHomologyIso p k f n G hG i).hom := by
  let : QuasiIso (CoveringPresentationResolution.augmentation.{u + 1, u} (BoundedCrystalline.Site.topology f n) R F) :=
    CoveringPresentationResolution.augmentation_quasiIso (BoundedCrystalline.Site.topology f n) R F hF
  let : QuasiIso (CoveringPresentationResolution.augmentation.{u + 1, u} (BoundedCrystalline.Site.topology f n) R G) :=
    CoveringPresentationResolution.augmentation_quasiIso (BoundedCrystalline.Site.topology f n) R G hG
  exact Balanced.FrameRefinement.homology.{u + 1, u, u + 2} F G ρ α R (BoundedCrystalline.Site.topology f n) H
    (CechCup.resolution p k f n)
    (BoundedFrame.ResolutionAcyclicity.subsingleton p k f n F)
    (BoundedFrame.ResolutionAcyclicity.subsingleton p k f n G) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.FrameRefinement
