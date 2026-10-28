import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CechResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamZariski

/-! # Cech Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechCohomology

noncomputable section

/-!
# IntegralComparison: actual finite-cover models for every bounded crystalline cohomology group
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] (n : ℕ)

def resolution : InjectiveResolution
    (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
      (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n) :=
  injectiveResolution _

def complex : CochainComplex (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  Bounded.CechResolution.total (Witt.Crystalline.wittStructureMap p k X) n (resolution p k X n)
    (DeRhamZariski.opens k X)

def homologyIso (i : ℕ) : (complex p k X n).homology i ≅
    ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
        (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n i) :=
  Bounded.CechResolution.homologyIso (Witt.Crystalline.wittStructureMap p k X) n (resolution p k X n)
    (DeRhamZariski.opens k X) (DeRhamZariski.cover k X) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechCohomology
