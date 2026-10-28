import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareMapEquality

/-! # Square Module Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareModuleMaps

noncomputable section

/-! Restrict a map upstairs to a commutative square, retaining the canonical
comparison between the two iterated pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X X' Y Y' : Scheme.{u}}

def pullbackSquareModuleMap (a : X' ⟶ X) (b : Y' ⟶ Y) (f : Y ⟶ X) (g : Y' ⟶ X')
    (h : g ≫ a = b ≫ f) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj M) ⟶
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj N) :=
  (SquareMapEquality.modulePullbackSquareIso a b f g h).hom.app M ≫ (Scheme.Modules.pullback b).map φ ≫
    (SquareMapEquality.modulePullbackSquareIso a b f g h).inv.app N

theorem pullbackSquareModuleMap_of_pullback (a : X' ⟶ X) (b : Y' ⟶ Y)
    (f : Y ⟶ X) (g : Y' ⟶ X') (h : g ≫ a = b ≫ f) {M N : X.Modules} (φ : M ⟶ N) :
    pullbackSquareModuleMap a b f g h ((Scheme.Modules.pullback f).map φ) =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback a).map φ) := by
  let e := SquareMapEquality.modulePullbackSquareIso a b f g h
  exact (congrArg (fun k => k ≫ e.inv.app N) (e.hom.naturality φ).symm).trans
    (by simp only [Category.assoc, e.hom_inv_id_app, Category.comp_id]; rfl)

theorem pullbackSquareModuleMap_comp (a : X' ⟶ X) (b : Y' ⟶ Y)
    (f : Y ⟶ X) (g : Y' ⟶ X') (h : g ≫ a = b ≫ f) {M N Q : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (ψ : (Scheme.Modules.pullback f).obj N ⟶ (Scheme.Modules.pullback f).obj Q) :
    pullbackSquareModuleMap a b f g h (φ ≫ ψ) =
      pullbackSquareModuleMap a b f g h φ ≫ pullbackSquareModuleMap a b f g h ψ := by
  unfold pullbackSquareModuleMap
  rw [(Scheme.Modules.pullback b).map_comp]
  simp only [Category.assoc, (SquareMapEquality.modulePullbackSquareIso a b f g h).inv_hom_id_app_assoc]

theorem pullbackSquareModuleMap_isIso (a : X' ⟶ X) (b : Y' ⟶ Y)
    (f : Y ⟶ X) (g : Y' ⟶ X') (h : g ≫ a = b ≫ f) {M N : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) [IsIso φ] :
    IsIso (pullbackSquareModuleMap a b f g h φ) :=
  inferInstanceAs (IsIso ((SquareMapEquality.modulePullbackSquareIso a b f g h).hom.app M ≫
    (Scheme.Modules.pullback b).map φ ≫ (SquareMapEquality.modulePullbackSquareIso a b f g h).inv.app N))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareModuleMaps
