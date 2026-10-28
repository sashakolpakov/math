import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ResolutionAcyclicity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCohomology

/-! # Resolution Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ResolutionCohomology

noncomputable section

/-! Global frame resolutions compute the original bounded crystalline Ext groups in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  Acyclic.ChainCohomology.complex R (BoundedCrystalline.CrystallineCohomology.structureSheaf f n)
    (CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology f n) R F)

def homologyIso (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U) (i : ℕ) :
    (complex p k f n F).homology i ≅
      ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) := by
  let h : QuasiIso (CoveringPresentationResolution.augmentation.{u + 1, u} (BoundedCrystalline.Site.topology f n) R F) :=
    CoveringPresentationResolution.augmentation_quasiIso.{u + 1, u} (BoundedCrystalline.Site.topology f n) R F hcover
  exact Acyclic.ChainCohomology.homologyIso R (BoundedCrystalline.CrystallineCohomology.structureSheaf f n)
    (CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology f n) R F)
    (CoveringPresentationResolution.augmentation.{u + 1, u} (BoundedCrystalline.Site.topology f n) R F)
    (ResolutionAcyclicity.subsingleton p k f n F) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ResolutionCohomology
