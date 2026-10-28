import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineBasePointSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UniversalGlobalSections

/-! # Trivial Bundle Section Surjectivity -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TrivialBundleSectionSurjectivity.Construction

noncomputable section

/-! Sections of a trivial bundle lift when all target functions come from a surjective base map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

universe u

theorem modulePullback_sections_surjective_of_iso
    {X Y : Scheme.{u}} (f : Y ⟶ X) {M N : X.Modules} (e : M ≅ N)
    (hN : Function.Surjective (PullbackModuleSections.Construction.modulePullbackGlobalSection f N)) :
    Function.Surjective (PullbackModuleSections.Construction.modulePullbackGlobalSection f M) := by
  let eX := ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)
  let eY := ConcreteCategory.bijective_of_isIso (((Scheme.Modules.pullback f).mapIso e).hom.app ⊤)
  intro y
  obtain ⟨n, hn⟩ := hN (((Scheme.Modules.pullback f).map e.hom).app ⊤ y)
  obtain ⟨m, hm⟩ := eX.surjective n
  refine ⟨m, eY.injective ?_⟩
  exact (PullbackModuleSections.Construction.modulePullbackGlobalSection_naturality f e.hom m).trans
    ((congrArg (PullbackModuleSections.Construction.modulePullbackGlobalSection f N) hm).trans hn)

theorem structureSheaf_sections_surjective_of_appTop
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Function.Surjective f.appTop) :
    Function.Surjective (PullbackModuleSections.Construction.modulePullbackGlobalSection f (LineBundle.Construction.structureSheafModule X)) := by
  let e := ConcreteCategory.bijective_of_isIso ((LineBundle.Construction.pullbackStructureSheafIso f).hom.app ⊤)
  intro y
  obtain ⟨x, hx⟩ := hf ((LineBundle.Construction.pullbackStructureSheafIso f).hom.app ⊤ y)
  exact ⟨x, e.injective ((PullbackModuleSections.Construction.modulePullbackGlobalSection_unit f x).trans hx)⟩

theorem appTop_surjective_of_base_square
    {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (h : f ≫ π = ρ ≫ g) (hg : Function.Surjective g.appTop)
    (hρ : Function.Surjective ρ.appTop) : Function.Surjective f.appTop := by
  have hs := congrArg (fun q : Y ⟶ S ↦ q.appTop) h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hs
  intro y
  obtain ⟨t, ht⟩ := hρ y
  obtain ⟨s, hs'⟩ := hg t
  exact ⟨π.appTop s, (ConcreteCategory.congr_hom hs s).trans
    ((congrArg ρ.appTop hs').trans ht)⟩

theorem affineBasePoint_appTop_surjective
    {S : Scheme.{u}} [IsAffine S] {A : Type u} [CommRing A]
    (a : Γ(S, ⊤) →+* A) (ha : Function.Surjective a) :
    Function.Surjective (AffineBasePointSections.Construction.affineBasePoint a).appTop := by
  intro y
  obtain ⟨x, hx⟩ := ha ((Scheme.ΓSpecIso (.of A)).hom y)
  refine ⟨x, (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom).injective ?_⟩
  exact (ConcreteCategory.congr_hom (AffineBasePointSections.Construction.affineBasePoint_appTop a) x).trans hx

theorem trivialBundle_sections_surjective_of_base_square
    {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    (h : f ≫ π = ρ ≫ g) (M : X.Modules) (e : M ≅ LineBundle.Construction.structureSheafModule X)
    (hg : Function.Surjective g.appTop) (hρ : Function.Surjective ρ.appTop) :
    Function.Surjective (PullbackModuleSections.Construction.modulePullbackGlobalSection f M) :=
  modulePullback_sections_surjective_of_iso f e
    (structureSheaf_sections_surjective_of_appTop f (appTop_surjective_of_base_square f π ρ g h hg hρ))

theorem trivialBundle_product_sections_surjective
    {k : Type u} [Field k] [IsAlgClosed k]
    (S T X : Over (Spec (.of k))) [IsProper X.hom] [IsIntegral X.left]
    (g : T ⟶ S) (hg : Function.Surjective g.left.appTop)
    (M : (S ⊗ X).left.Modules) (e : M ≅ LineBundle.Construction.structureSheafModule (S ⊗ X).left) :
    Function.Surjective (PullbackModuleSections.Construction.modulePullbackGlobalSection (g ⊗ₘ 𝟙 X).left M) := by
  have : IsIso (fst T X).left.appTop := UniversalGlobalSections.Construction.isIso_properBaseChange_app T X ⊤
  have h : (g ⊗ₘ 𝟙 X).left ≫ (fst S X).left = (fst T X).left ≫ g.left :=
    congrArg (fun a : T ⊗ X ⟶ S ↦ a.left) (tensorHom_fst g (𝟙 X))
  exact trivialBundle_sections_surjective_of_base_square (g ⊗ₘ 𝟙 X).left
    (fst S X).left (fst T X).left g.left h M e hg
      (ConcreteCategory.bijective_of_isIso (fst T X).left.appTop).surjective

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TrivialBundleSectionSurjectivity.Construction
