import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MapAllStalkDetection

/-! # Ring Pullback Map Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.RingPullbackMapDetection

noncomputable section

/-! Equality after every local-ring-valued base change detects arbitrary scheme maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem schemeMap_eq_of_localRingPullbacks {X S Y : Scheme.{u}}
    (p : X ⟶ S) (f g : X ⟶ Y)
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] (b : Spec (.of A) ⟶ S),
      pullback.fst p b ≫ f = pullback.fst p b ≫ g) : f = g := by
  apply MapAllStalkDetection.schemeMap_eq_of_allStalkPoints
  intro x
  have hlocal : IsLocalRing (X.presheaf.stalk x) := X.toLocallyRingedSpace.isLocalRing x
  let r := X.fromSpecStalk x
  let b := r ≫ p
  let l := pullback.lift r (𝟙 _) (Category.id_comp b).symm
  have hl : l ≫ pullback.fst p b = r := pullback.lift_fst _ _ _
  have H := congrArg (fun q => l ≫ q) (@h (X.presheaf.stalk x) _ hlocal b)
  change l ≫ pullback.fst p b ≫ f = l ≫ pullback.fst p b ≫ g at H
  rw [← Category.assoc, ← Category.assoc, hl] at H
  exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.RingPullbackMapDetection
