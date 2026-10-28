import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-! # Over Effective Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverEffectiveDescent

noncomputable section

/-! Descending a morphism over the base along an underlying effective epimorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem over_factor_of_effectiveEpi {S : Scheme.{u}} {X Y Z : Over S}
    (f : X ⟶ Y) [EffectiveEpi f.left] (m : X ⟶ Z)
    (h : ∀ {T : Over S} (a b : T ⟶ X), a ≫ f = b ≫ f → a ≫ m = b ≫ m) :
    ∃! d : Y ⟶ Z, f ≫ d = m := by
  have hs {T : Scheme.{u}} (a b : T ⟶ X.left) (hab : a ≫ f.left = b ≫ f.left) :
      a ≫ m.left = b ≫ m.left := by
    let V : Over S := Over.mk (a ≫ X.hom)
    let a' : V ⟶ X := Over.homMk a rfl
    have hb : b ≫ X.hom = a ≫ X.hom := by
      have he := congrArg (fun v : T ⟶ Y.left => v ≫ Y.hom) hab
      simpa only [Category.assoc, f.w] using he.symm
    let b' : V ⟶ X := Over.homMk b hb
    exact congrArg (fun v : V ⟶ Z => v.left) (h a' b' (Over.OverMorphism.ext hab))
  let d := EffectiveEpi.desc f.left m.left hs
  have hd : f.left ≫ d = m.left := EffectiveEpi.fac f.left m.left hs
  have hw : d ≫ Z.hom = Y.hom := by
    apply (cancel_epi f.left).mp
    rw [← Category.assoc, hd, m.w, f.w]
  refine ⟨Over.homMk d hw, Over.OverMorphism.ext hd, ?_⟩
  intro e he
  apply Over.OverMorphism.ext
  exact EffectiveEpi.uniq f.left m.left hs e.left
    (congrArg (fun v : X ⟶ Z => v.left) he)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverEffectiveDescent
