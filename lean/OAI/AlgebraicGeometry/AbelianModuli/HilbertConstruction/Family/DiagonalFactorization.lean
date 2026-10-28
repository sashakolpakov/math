import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ProductProjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Diagonal Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.DiagonalFactorization

noncomputable section

/-! Equality of two family morphisms after base change is exactly unique factorization of their paired map through the actual closed diagonal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

def familyDiagonal {S : Scheme.{u}} (Y : Over S) : Y ⟶ Y ⊗ Y := MorphismGraphFamilies.familyGraph (𝟙 Y)

theorem familyDiagonal_fst {S : Scheme.{u}} (Y : Over S) : familyDiagonal Y ≫ fst Y Y = 𝟙 Y :=
  lift_fst (𝟙 Y) (𝟙 Y)

theorem familyDiagonal_snd {S : Scheme.{u}} (Y : Over S) : familyDiagonal Y ≫ snd Y Y = 𝟙 Y :=
  lift_snd (𝟙 Y) (𝟙 Y)

instance familyDiagonal_closed {S : Scheme.{u}} (Y : Over S) [IsSeparated Y.hom] :
    IsClosedImmersion (familyDiagonal Y).left := inferInstanceAs (IsClosedImmersion (MorphismGraphFamilies.familyGraph (𝟙 Y)).left)

theorem overPullbackProduct_hom_ext {S T : Scheme.{u}} (f : T ⟶ S) (A B : Over S) {W : Over T}
    (a b : W ⟶ (Over.pullback f).obj (A ⊗ B))
    (hf : a ≫ (Over.pullback f).map (fst A B) = b ≫ (Over.pullback f).map (fst A B))
    (hs : a ≫ (Over.pullback f).map (snd A B) = b ≫ (Over.pullback f).map (snd A B)) : a = b := by
  apply (cancel_mono (Functor.Monoidal.μIso (Over.pullback f) A B).inv).mp
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Pullback.ProductProjection.overPullbackProductIso_inv_fst, Category.assoc, Pullback.ProductProjection.overPullbackProductIso_inv_fst]
    exact hf
  · rw [Category.assoc, Pullback.ProductProjection.overPullbackProductIso_inv_snd, Category.assoc, Pullback.ProductProjection.overPullbackProductIso_inv_snd]
    exact hs

theorem overPullback_equal_iff_diagonal_factorization {S T : Scheme.{u}} {X Y : Over S}
    [IsSeparated Y.hom] (f : T ⟶ S) (u v : X ⟶ Y) :
    (Over.pullback f).map u = (Over.pullback f).map v ↔
      ∃! h : (Over.pullback f).obj X ⟶ (Over.pullback f).obj Y,
        h ≫ (Over.pullback f).map (familyDiagonal Y) = (Over.pullback f).map (lift u v) := by
  let F := Over.pullback f
  have hd₁ : F.map (familyDiagonal Y) ≫ F.map (fst Y Y) = 𝟙 (F.obj Y) := by
    rw [← F.map_comp, familyDiagonal_fst, F.map_id]
  have hd₂ : F.map (familyDiagonal Y) ≫ F.map (snd Y Y) = 𝟙 (F.obj Y) := by
    rw [← F.map_comp, familyDiagonal_snd, F.map_id]
  have hp₁ : F.map (lift u v) ≫ F.map (fst Y Y) = F.map u := by
    rw [← F.map_comp, lift_fst]
  have hp₂ : F.map (lift u v) ≫ F.map (snd Y Y) = F.map v := by
    rw [← F.map_comp, lift_snd]
  have : IsClosedImmersion (F.map (familyDiagonal Y)).left := Projective.PresentationBaseChange.overPullback_map_closed (familyDiagonal Y) f
  have : Mono (F.map (familyDiagonal Y)) := Over.mono_of_mono_left _
  constructor
  · intro huv
    have hh : F.map u ≫ F.map (familyDiagonal Y) = F.map (lift u v) := by
      apply overPullbackProduct_hom_ext f Y Y
      · rw [Category.assoc, hd₁, Category.comp_id, hp₁]
      · rw [Category.assoc, hd₂, Category.comp_id, hp₂]
        exact huv
    exact ⟨F.map u, hh, fun _ hk => (cancel_mono _).mp (hk.trans hh.symm)⟩
  · rintro ⟨h, hh, _⟩
    have h₁ := congrArg (fun k => k ≫ F.map (fst Y Y)) hh
    have h₂ := congrArg (fun k => k ≫ F.map (snd Y Y)) hh
    rw [Category.assoc, hd₁, Category.comp_id, hp₁] at h₁
    rw [Category.assoc, hd₂, Category.comp_id, hp₂] at h₂
    exact h₁.symm.trans h₂

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.DiagonalFactorization
