import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.RefinementExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechCohomology

/-! # Cech Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechRefinement

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

def map : CechCohomology.complex p k f n G ⟶
    CechCohomology.complex p k f n F :=
  FrameCech.RefinementExt.liftedMap.{u + 1, u, u + 2} F G ρ α R (BoundedCrystalline.Site.topology f n) H

theorem homology
    (hF : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U)
    (hG : ∀ U, CoveringObjectsSheafDetection.sieve G U ∈ BoundedCrystalline.Site.topology f n U) (i : ℕ) :
    HomologicalComplex.homologyMap (map p k f n F G ρ α) i ≫
      (CechCohomology.homologyIso p k f n F hF i).hom =
        (CechCohomology.homologyIso p k f n G hG i).hom := by
  let : QuasiIso (CoveringPresentationResolution.augmentation.{u + 1, u} (BoundedCrystalline.Site.topology f n) R F) :=
    CoveringPresentationResolution.augmentation_quasiIso (BoundedCrystalline.Site.topology f n) R F hF
  let : QuasiIso (CoveringPresentationResolution.augmentation.{u + 1, u} (BoundedCrystalline.Site.topology f n) R G) :=
    CoveringPresentationResolution.augmentation_quasiIso (BoundedCrystalline.Site.topology f n) R G hG
  exact FrameCech.RefinementExt.homology.{u + 1, u, u + 2} F G ρ α R (BoundedCrystalline.Site.topology f n) H
    (ResolutionAcyclicity.subsingleton p k f n F)
    (ResolutionAcyclicity.subsingleton p k f n G) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechRefinement
