import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo

/-! # Open Section Geometric Pullback -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback

noncomputable section

/-! Pullback of native section algebras to an arbitrary smaller open subset. -/

namespace DeRhamPullback

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {R : Type u} [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  (U : Y.left.Opens) (V : X.left.Opens) (h : V ≤ f.left ⁻¹ᵁ U)

def sectionPullbackLE :
    letI := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y U
    letI := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X V
    Γ(Y.left, U) →ₐ[R] Γ(X.left, V) :=
  ((AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map (homOfLE h).op).hom.comp (DeRhamPullbackTo.DeRhamPullback.sectionPullback f U)

theorem sectionPullbackLE_toRingHom : (sectionPullbackLE f U V h).toRingHom = (f.left.appLE U V h).hom := rfl

def formsPullbackLE (n : ℕ) :
    (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Y n).obj (op U) ⟶
      (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op V) :=
  ModuleCat.ofHom (DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (sectionPullbackLE f U V h)) n)

theorem formsPullbackLE_eq (n : ℕ) : formsPullbackLE f U V h n =
    (DeRhamPullbackTo.DeRhamPullback.formsPullback f n).app (op U) ≫ (DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).map (homOfLE h).op := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact DeRhamGlobalId.DeRhamGlobal.formMap_comp (CommAlgCat.ofHom (DeRhamPullbackTo.DeRhamPullback.sectionPullback f U))
    ((AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map (homOfLE h).op) n ω

end DeRhamPullback

/-! A commuting square of schemes induces a commuting square on sections of arbitrary compatible opens. -/

namespace SectionGeometricSquare

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem appLE_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

theorem square {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂)
    (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂) (h : f₁ ≫ u = v ≫ f₂)
    (U : X₂.Opens) (V : X₁.Opens) (W : Y₂.Opens) (T : Y₁.Opens)
    (hu : V ≤ u ⁻¹ᵁ U) (hv : T ≤ v ⁻¹ᵁ W)
    (h₁ : T ≤ f₁ ⁻¹ᵁ V) (h₂ : W ≤ f₂ ⁻¹ᵁ U) :
    u.appLE U V hu ≫ f₁.appLE V T h₁ = f₂.appLE U W h₂ ≫ v.appLE W T hv :=
  (Scheme.Hom.appLE_comp_appLE f₁ u U V T hu h₁).trans
    ((appLE_congr h U T _ _).trans (Scheme.Hom.appLE_comp_appLE v f₂ U W T h₂ hv).symm)

theorem preimage_le {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂)
    (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂) (h : f₁ ≫ u = v ≫ f₂)
    (U : X₂.Opens) (V : X₁.Opens) (hu : V ≤ u ⁻¹ᵁ U) :
    f₁ ⁻¹ᵁ V ≤ v ⁻¹ᵁ (f₂ ⁻¹ᵁ U) := by
  have he : f₁ ⁻¹ᵁ (u ⁻¹ᵁ U) = v ⁻¹ᵁ (f₂ ⁻¹ᵁ U) :=
    congrArg (fun g : Y₁ ⟶ X₂ => g ⁻¹ᵁ U) h
  exact ((TopologicalSpace.Opens.map f₁.base).map (homOfLE hu)).le.trans he.le

end SectionGeometricSquare

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback
