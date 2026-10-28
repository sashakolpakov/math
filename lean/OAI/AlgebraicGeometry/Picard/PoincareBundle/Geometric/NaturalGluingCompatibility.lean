import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

/-! # Natural Gluing Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.NaturalGluingCompatibility

noncomputable section

/-!
# Compatibility with natural geometric gluing before choosing affine coordinates
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X)

/-- The ordinary compatibility equation for a component of a natural geometric gluing map. -/
def CompatibleWith {N : Y.Modules} {M : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj N ⟶ M)
    (σ : (Scheme.Modules.pullback p).obj M ⟶ (Scheme.Modules.pullback q).obj M)
    (η : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback p ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback q) : Prop :=
  (Scheme.Modules.pullback p).map φ ≫ σ =
    η.hom.app N ≫ (Scheme.Modules.pullback q).map φ

/-- The actual invariant comparison satisfies ordinary standard geometric compatibility. -/
theorem comparison_compatible (h : p ≫ f = q ≫ f) (M : X.Modules)
    (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M) :
    CompatibleWith f p q (CechInvariant.comparison f p q h M σ) σ.hom
      (Cech.MateNormalization.standardGluing f p q h) :=
  Cech.MateNormalization.comparison_standard_compatible f p q h M σ

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.NaturalGluingCompatibility
