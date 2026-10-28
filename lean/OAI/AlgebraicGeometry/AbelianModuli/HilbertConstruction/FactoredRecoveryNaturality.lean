import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredBaseRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Factored Recovery Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredRecoveryNaturality

noncomputable section

/-! Factoring Cartesian recovery through an intermediate base preserves every compatible morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem factoredBaseRecovery_natural
    {S T U : Scheme.{u}} (r : T ⟶ U) (c : U ⟶ S)
    {A B : Over T} {X Y : Over S} (f : A ⟶ B) (g : X ⟶ Y)
    (qA : A.left ⟶ X.left) (qB : B.left ⟶ Y.left)
    (hA : IsPullback qA A.hom X.hom (r ≫ c)) (hB : IsPullback qB B.hom Y.hom (r ≫ c))
    (hw : qA ≫ g.left = f.left ≫ qB) :
    FactoredBaseRecovery.factoredBaseRecovery qA A.hom X.hom r c hA ≫ ((Over.pullback c).map g).left =
      f.left ≫ FactoredBaseRecovery.factoredBaseRecovery qB B.hom Y.hom r c hB := by
  let a : A.left ⟶ pullback X.hom c := FactoredBaseRecovery.factoredBaseRecovery qA A.hom X.hom r c hA
  let b : B.left ⟶ pullback Y.hom c := FactoredBaseRecovery.factoredBaseRecovery qB B.hom Y.hom r c hB
  let k : pullback X.hom c ⟶ pullback Y.hom c := ((Over.pullback c).map g).left
  let f₀ : A.left ⟶ B.left := f.left
  let g₀ : X.left ⟶ Y.left := g.left
  have hk₁ : k ≫ pullback.fst Y.hom c = pullback.fst X.hom c ≫ g₀ :=
    (Projective.PresentationBaseChange.overPullback_map_isPullback g c).w.symm
  have hk₂ : k ≫ pullback.snd Y.hom c = pullback.snd X.hom c := ((Over.pullback c).map g).w
  have ha₁ : a ≫ pullback.fst X.hom c = qA := FactoredBaseRecovery.factoredBaseRecovery_fst qA A.hom X.hom r c hA
  have hb₁ : b ≫ pullback.fst Y.hom c = qB := FactoredBaseRecovery.factoredBaseRecovery_fst qB B.hom Y.hom r c hB
  have ha₂ : a ≫ pullback.snd X.hom c = A.hom ≫ r := FactoredBaseRecovery.factoredBaseRecovery_snd qA A.hom X.hom r c hA
  have hb₂ : b ≫ pullback.snd Y.hom c = B.hom ≫ r := FactoredBaseRecovery.factoredBaseRecovery_snd qB B.hom Y.hom r c hB
  change a ≫ k = f₀ ≫ b
  apply pullback.hom_ext
  · rw [Category.assoc, hk₁, ← Category.assoc, ha₁, Category.assoc, hb₁]
    exact hw
  · rw [Category.assoc, hk₂, ha₂, Category.assoc, hb₂, ← Category.assoc]
    exact (congrArg (fun p => p ≫ r) f.w).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredRecoveryNaturality
