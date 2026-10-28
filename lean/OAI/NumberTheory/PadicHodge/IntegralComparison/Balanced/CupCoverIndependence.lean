import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CupRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsProduct

/-! # Cup Cover Independence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupCoverIndependence

noncomputable section

/-! The actual augmentation-normalized bounded crystalline cup is
independent of the chosen genuine covering family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι κ : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (G : κ → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (hF : ∀ V, CoveringObjectsSheafDetection.sieve F V ∈ BoundedCrystalline.Site.topology f n V)
  (hG : ∀ V, CoveringObjectsSheafDetection.sieve G V ∈ BoundedCrystalline.Site.topology f n V)

theorem cup_eq (i j : ℕ)
    (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i)
    (y : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n j) :
    BalancedBounded.CechCup.cup p k f n F hF i j x y =
      BalancedBounded.CechCup.cup p k f n G hG i j x y := by
  let FG := CoveringObjectsProduct.family F G
  have hFG := CoveringObjectsProduct.covering (BoundedCrystalline.Site.topology f n) F G hF hG
  exact (BalancedBounded.CupRefinement.cup_eq p k f n FG F Prod.fst
    (fun _ => prod.fst) hFG hF i j x y).symm.trans
    (BalancedBounded.CupRefinement.cup_eq p k f n FG G Prod.snd
      (fun _ => prod.snd) hFG hG i j x y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupCoverIndependence
