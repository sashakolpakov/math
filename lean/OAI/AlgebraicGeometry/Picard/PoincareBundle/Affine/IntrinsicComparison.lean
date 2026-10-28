import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingPullback

/-! # Intrinsic Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.IntrinsicComparison.Intrinsic

noncomputable section

/-!
# The affine pullback comparison is the native sheaf pullback formula
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingPullback

/-- The affine geometric gluing formula is exactly the native geometric pullback. -/
theorem geometricHom_eq_native {R S T : CommRingCat.{u}} {L : (Spec R).Modules}
    (f g : R ⟶ S) (k : S ⟶ T)
    (a : (Scheme.Modules.pullback (Spec.map f)).obj L ⟶
      (Scheme.Modules.pullback (Spec.map g)).obj L) :
    GluingPullback.geometricHom f g k a = Geometric.DescentEquations.nativePullback a (Spec.map k)
      (Spec.map (f ≫ k)) (Spec.map (g ≫ k))
      (Spec.map_comp f k).symm (Spec.map_comp g k).symm := by
  have h₁ : Composition.geometricCompositionIso f k =
      Scheme.Modules.pullbackComp (Spec.map k) (Spec.map f) ≪≫
        Scheme.Modules.pullbackCongr (Spec.map_comp f k).symm := rfl
  have h₂ : Composition.geometricCompositionIso g k =
      Scheme.Modules.pullbackComp (Spec.map k) (Spec.map g) ≪≫
        Scheme.Modules.pullbackCongr (Spec.map_comp g k).symm := rfl
  exact congrArg₂ (fun
    (u : Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map k) ≅
      Scheme.Modules.pullback (Spec.map (f ≫ k)))
    (v : Scheme.Modules.pullback (Spec.map g) ⋙ Scheme.Modules.pullback (Spec.map k) ≅
      Scheme.Modules.pullback (Spec.map (g ≫ k))) =>
    u.inv.app L ≫ (Scheme.Modules.pullback (Spec.map k)).map a ≫ v.hom.app L) h₁ h₂

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.IntrinsicComparison.Intrinsic
