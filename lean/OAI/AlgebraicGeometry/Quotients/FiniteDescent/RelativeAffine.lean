import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperAffine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Relative Affine -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeAffine.Construction.RelativeAffineRigidity

noncomputable section

/-! Affine-target rigidity for proper smooth morphisms with connected geometric fibers and a section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S Y : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f]
variable [GeometricallyConnected f] (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
variable [IsAffine Y] (h : X ⟶ Y)

include he

theorem residuePoint_eq (x : X) :
    X.fromSpecResidueField x ≫ h = X.fromSpecResidueField x ≫ f ≫ e ≫ h := by
  let a := X.fromSpecResidueField x
  let k := a ≫ f
  let P := pullback f k
  let π : P ⟶ Spec (X.residueField x) := pullback.snd f k
  have hπs : Smooth π := inferInstanceAs (Smooth (pullback.snd f k))
  have hπp : IsProper π := inferInstanceAs (IsProper (pullback.snd f k))
  have : GeometricallyConnected π := inferInstanceAs (GeometricallyConnected (pullback.snd f k))
  have : IsReduced P := @SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field
    (X.residueField x) inferInstance P π hπs
  have : ConnectedSpace P := GeometricallyConnected.connectedSpace_of_subsingleton π
  let a' : Spec (X.residueField x) ⟶ P := pullback.lift a (𝟙 _) (by simp [k])
  let e' : Spec (X.residueField x) ⟶ P :=
    pullback.lift (k ≫ e) (𝟙 _) (by simp [Category.assoc, he])
  have ha' : a' ≫ π = 𝟙 _ := pullback.lift_snd _ _ _
  have he' : e' ≫ π = 𝟙 _ := pullback.lift_snd _ _ _
  have : IsProper (Over.mk π).hom := hπp
  have : ConnectedSpace (Over.mk π).left := inferInstanceAs (ConnectedSpace P)
  have : IsReduced (Over.mk π).left := inferInstanceAs (IsReduced P)
  have H := ProperAffine.Construction.ProperAffineRigidity.points_eq (K := X.residueField x)
    (Over.mk π) (pullback.fst f k ≫ h) a' e' ha' he'
  have h₁ : a' ≫ pullback.fst f k = a := pullback.lift_fst _ _ _
  have h₂ : e' ≫ pullback.fst f k = k ≫ e := pullback.lift_fst _ _ _
  rw [← Category.assoc, ← Category.assoc, h₁, h₂, Category.assoc] at H
  exact H

theorem factor [IsReduced X] : h = f ≫ e ≫ h := by
  apply ext_of_fromSpecResidueField_eq h (f ≫ e ≫ h) (terminal.from Y)
    Set.univ dense_univ
  · intro x _
    exact residuePoint_eq f e he h x
  · exact terminal.hom_ext _ _

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeAffine.Construction.RelativeAffineRigidity
