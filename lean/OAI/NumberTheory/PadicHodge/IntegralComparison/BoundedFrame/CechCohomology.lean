import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Ext
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ResolutionCohomology

/-! # Cech Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechCohomology

noncomputable section

/-! The native frame Čech complex computes original bounded crystalline cohomology in all degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).obj
    (CechComplex.complex f n F)

def comparison : ResolutionCohomology.complex p k f n F ≅ complex p k f n F :=
  FrameCech.Ext.Comparison.comparison.{u + 1, u, u + 2} F R (BoundedCrystalline.Site.topology f n)
    (BoundedCrystalline.CrystallineCohomology.structureSheaf f n)

def homologyIso (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U) (i : ℕ) :
    (complex p k f n F).homology i ≅ ModuleCat.of R
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (comparison p k f n F).symm ≪≫
    ResolutionCohomology.homologyIso p k f n F hcover i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechCohomology
