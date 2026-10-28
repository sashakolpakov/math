import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Square Map Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareMapEquality

noncomputable section

/-! Equality of module maps after pullback transports across a commutative square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X X' Y Y' : Scheme.{u}}

def modulePullbackSquareIso (a : X' ⟶ X) (b : Y' ⟶ Y) (f : Y ⟶ X) (g : Y' ⟶ X')
    (h : g ≫ a = b ≫ f) :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback b :=
  Scheme.Modules.pullbackComp g a ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp b f).symm

theorem pullbackSquare_map_eq (a : X' ⟶ X) (b : Y' ⟶ Y) (f : Y ⟶ X) (g : Y' ⟶ X')
    (h : g ≫ a = b ≫ f) {M N : X.Modules} (φ ψ : M ⟶ N)
    (hφ : (Scheme.Modules.pullback f).map φ = (Scheme.Modules.pullback f).map ψ) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback a).map φ) =
      (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback a).map ψ) := by
  let e := modulePullbackSquareIso a b f g h
  apply (cancel_mono (e.hom.app N)).mp
  exact (e.hom.naturality φ).trans
    ((congrArg (fun k => e.hom.app M ≫ (Scheme.Modules.pullback b).map k) hφ).trans
      (e.hom.naturality ψ).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SquareMapEquality
