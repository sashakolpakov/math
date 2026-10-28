import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackComposition

/-! # Map Pullback Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackCongruence

noncomputable section

/-! Transport of pulled-back module maps along equality of the underlying scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

def moduleMapPullbackCongr {f g : Y ⟶ Z} (h : f = g) {M N : Z.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N :=
  Iso.homCongr ((Scheme.Modules.pullbackCongr h).app M)
    ((Scheme.Modules.pullbackCongr h).app N) φ

theorem moduleMapPullbackCongr_refl (f : Y ⟶ Z) {M N : Z.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    moduleMapPullbackCongr (rfl : f = f) φ = φ := by
  change (Iso.refl _).homCongr (Iso.refl _) φ = φ
  exact Iso.homCongr_refl φ

theorem moduleMapPullbackCongr_trans {f g h : Y ⟶ Z} (h₁ : f = g) (h₂ : g = h)
    {M N : Z.Modules} (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    moduleMapPullbackCongr h₂ (moduleMapPullbackCongr h₁ φ) =
      moduleMapPullbackCongr (h₁.trans h₂) φ := by
  subst g h
  simp only [moduleMapPullbackCongr_refl]

theorem moduleMapPullbackComp_congr_base (a : X ⟶ Y) {f g : Y ⟶ Z} (h : f = g)
    {M N : Z.Modules} (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    moduleMapPullbackCongr (congrArg (fun k => a ≫ k) h) (MapPullbackComposition.moduleMapPullbackComp a f φ) =
      MapPullbackComposition.moduleMapPullbackComp a g (moduleMapPullbackCongr h φ) := by
  subst g
  simp only [moduleMapPullbackCongr_refl]

theorem moduleMapPullbackCongr_of_map {f g : Y ⟶ Z} (h : f = g) {M N : Z.Modules} (φ : M ⟶ N) :
    moduleMapPullbackCongr h ((Scheme.Modules.pullback f).map φ) =
      (Scheme.Modules.pullback g).map φ :=
  MapPullbackComposition.moduleMap_homCongr_naturality _ _ (Scheme.Modules.pullbackCongr h) φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackCongruence
