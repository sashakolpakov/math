import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

/-! # Kernel Pair Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.KernelPairCompatibility

noncomputable section

/-! Original-base gluing compatibility holds on the actual scheme-theoretic kernel pair. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

variable {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
  (D E : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f.left))
  (e : D.obj PUnit.unit ≅ E.obj PUnit.unit)

/-- The actual fiber-product relation is among the original-base test schemes. -/
theorem compatibility
    (h : ∀ (T : Over S) (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x.left).map e.hom ≫ E.hom q.left
        (i₁ := PUnit.unit) (i₂ := PUnit.unit) x.left y.left
        (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
      D.hom q.left (i₁ := PUnit.unit) (i₂ := PUnit.unit) x.left y.left
        (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) ≫
          (Scheme.Modules.pullback y.left).map e.hom) :
    (Scheme.Modules.pullback (pullback.fst f.left f.left)).map e.hom ≫ (Geometric.CechInvariant.relationGluing f.left E).hom =
      (Geometric.CechInvariant.relationGluing f.left D).hom ≫ (Scheme.Modules.pullback (pullback.snd f.left f.left)).map e.hom := by
  let U : Over S := Over.mk ((pullback.snd f.left f.left ≫ f.left) ≫ B.hom)
  let q : U ⟶ B := Over.homMk (pullback.snd f.left f.left ≫ f.left) rfl
  let x : U ⟶ A := Over.homMk (pullback.fst f.left f.left) (by
    change pullback.fst f.left f.left ≫ A.hom = (pullback.snd f.left f.left ≫ f.left) ≫ B.hom
    rw [← pullback.condition, Category.assoc, Over.w f])
  let y : U ⟶ A := Over.homMk (pullback.snd f.left f.left) (by
    change pullback.snd f.left f.left ≫ A.hom = (pullback.snd f.left f.left ≫ f.left) ≫ B.hom
    rw [Category.assoc, Over.w f])
  exact h U q x y (Over.OverMorphism.ext pullback.condition) (Over.OverMorphism.ext rfl)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.KernelPairCompatibility
