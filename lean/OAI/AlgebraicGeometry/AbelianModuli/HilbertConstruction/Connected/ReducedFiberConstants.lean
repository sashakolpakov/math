import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Reduced Fiber Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedFiberConstants

noncomputable section

/-! Affine-valued maps on a proper geometrically connected reduced family with a section are constant along each residue-field fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S Y : Scheme.{u}}

theorem properConnectedReducedFamily_affineMap_residue (p : X ⟶ S)
    [UniversallyClosed p] [GeometricallyConnected p] [GeometricallyReduced p] (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (f : X ⟶ Y) [IsAffine Y] (z : X) :
    X.fromSpecResidueField z ≫ f = X.fromSpecResidueField z ≫ (p ≫ σ ≫ f) := by
  let b := X.fromSpecResidueField z ≫ p
  let q : pullback p b ⟶ Spec (.of (X.residueField z)) := pullback.snd p b
  let j : pullback p b ⟶ X := pullback.fst p b
  have : UniversallyClosed q := inferInstanceAs (UniversallyClosed (pullback.snd p b))
  have : ConnectedSpace (pullback p b : Scheme.{u}) :=
    GeometricallyConnected.geometrically_connectedSpace b j q (.of_hasPullback p b)
  have : IsReduced (pullback p b) :=
    GeometricallyReduced.geometrically_isReduced b j q (.of_hasPullback p b)
  have hs : (b ≫ σ) ≫ p = (𝟙 _) ≫ b := by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp]
  let s : Spec (.of (X.residueField z)) ⟶ pullback p b := pullback.lift (b ≫ σ) (𝟙 _) hs
  have hsq : s ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have hsj : s ≫ j = b ≫ σ := pullback.lift_fst _ _ _
  have ha : X.fromSpecResidueField z ≫ p = (𝟙 _) ≫ b := (Category.id_comp b).symm
  let a : Spec (.of (X.residueField z)) ⟶ pullback p b :=
    pullback.lift (X.fromSpecResidueField z) (𝟙 _) ha
  have haq : a ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have haj : a ≫ j = X.fromSpecResidueField z := pullback.lift_fst _ _ _
  have H := Proper.ConnectedReducedConstants.properConnectedReduced_map_eq_constant q (j ≫ f) s hsq
  calc
    _ = a ≫ (j ≫ f) := by rw [← Category.assoc, haj]
    _ = a ≫ (q ≫ s ≫ (j ≫ f)) := congrArg (fun k => a ≫ k) H
    _ = b ≫ σ ≫ f := by
      rw [← Category.assoc a q, haq, Category.id_comp, ← Category.assoc s j, hsj, Category.assoc]
    _ = _ := Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedFiberConstants
