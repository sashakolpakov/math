import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionPullback

/-! # Geometric Restriction -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.Section.GeometricRestriction.SectionGeometricSquare

/-! A commuting square of schemes induces a commuting square on sections of arbitrary compatible opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

theorem square {X₁ X₂ Y₁ Y₂ : Scheme.{0}} (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂)
    (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂) (h : f₁ ≫ u = v ≫ f₂)
    (U : X₂.Opens) (V : X₁.Opens) (W : Y₂.Opens) (T : Y₁.Opens)
    (hu : V ≤ u ⁻¹ᵁ U) (hv : T ≤ v ⁻¹ᵁ W)
    (h₁ : T ≤ f₁ ⁻¹ᵁ V) (h₂ : W ≤ f₂ ⁻¹ᵁ U) :
    u.appLE U V hu ≫ f₁.appLE V T h₁ = f₂.appLE U W h₂ ≫ v.appLE W T hv :=
  (Scheme.Hom.appLE_comp_appLE f₁ u U V T hu h₁).trans
    ((appLE_congr h U T _ _).trans (Scheme.Hom.appLE_comp_appLE v f₂ U W T h₂ hv).symm)

theorem preimage_le {X₁ X₂ Y₁ Y₂ : Scheme.{0}} (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂)
    (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂) (h : f₁ ≫ u = v ≫ f₂)
    (U : X₂.Opens) (V : X₁.Opens) (hu : V ≤ u ⁻¹ᵁ U) :
    f₁ ⁻¹ᵁ V ≤ v ⁻¹ᵁ (f₂ ⁻¹ᵁ U) := by
  have he : f₁ ⁻¹ᵁ (u ⁻¹ᵁ U) = v ⁻¹ᵁ (f₂ ⁻¹ᵁ U) :=
    congrArg (fun g : Y₁ ⟶ X₂ => g ⁻¹ᵁ U) h
  exact ((TopologicalSpace.Opens.map f₁.base).map (homOfLE hu)).le.trans he.le

end NumberTheory.PadicHodge.GeometricComparison.Section.GeometricRestriction.SectionGeometricSquare

namespace NumberTheory.PadicHodge.GeometricComparison.Section.GeometricRestriction.SectionGeometricRestriction

/-! Pullback on sections commutes with restriction of both compatible
opens, retaining the original scheme section maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y)
  (U U' : Y.Opens) (V V' : X.Opens) (hU : U ≤ U') (hV : V ≤ V')
  (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U')

theorem square : f.appLE U' V' h' ≫ X.presheaf.map (homOfLE hV).op =
    Y.presheaf.map (homOfLE hU).op ≫ f.appLE U V h :=
  (f.appLE_map h' (homOfLE hV).op).trans (f.map_appLE h (homOfLE hU).op).symm

end NumberTheory.PadicHodge.GeometricComparison.Section.GeometricRestriction.SectionGeometricRestriction

end

end OAI
