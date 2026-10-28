import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingMorphismTransfer
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.NaturalGluingCompatibility

/-! # Natural Gluing Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.NaturalGluingCompatibility

noncomputable section

/-!
# Compatibility with a specified natural geometric gluing map
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (i j : S ⟶ T)
  {P : (Spec R).Modules} {M : (Spec S).Modules}
  (φ : (Scheme.Modules.pullback (Spec.map f)).obj P ⟶ M)
  (σ : (Scheme.Modules.pullback (Spec.map i)).obj M ⟶
    (Scheme.Modules.pullback (Spec.map j)).obj M)

/-- Ordinary geometric compatibility with the component of a specified natural gluing map. -/
def CompatibleWith
    (η : Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map i) ≅
      Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map j)) : Prop :=
  Geometric.NaturalGluingCompatibility.CompatibleWith (Spec.map f) (Spec.map i) (Spec.map j) φ σ η

/-- Express the proved affine gluing equation in the coordinate-independent compatibility form. -/
theorem of_equation
    (η : Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map i) ≅
      Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map j))
    (h : GluingMorphismTransfer.PreservesGeometricGluing i j φ (η.hom.app P) σ) :
    CompatibleWith f i j φ σ η := h

/-- Equal natural gluing maps impose exactly the same compatibility equation. -/
theorem congr
    {η θ : Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map i) ≅
      Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map j)} (h : η = θ) :
    CompatibleWith f i j φ σ η ↔ CompatibleWith f i j φ σ θ := by
  subst θ
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.NaturalGluingCompatibility
