import OAI.AlgebraicGeometry.Picard.Homomorphisms.FunctionDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeFunctions

/-! # Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction

noncomputable section

/-! Global functions descend through an epimorphism. In particular,
the universal global-functions property of an abelian family passes
through its actual finite-flat quotient and every further base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.FunctionDescent.Construction

universe u

theorem isIso_left_of_isIso_comp_of_injective
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B)
    [IsIso (f ≫ g)] (hg : Function.Injective g) : IsIso f := by
  have h := (ConcreteCategory.isIso_iff_bijective (f ≫ g)).mp inferInstance
  apply (ConcreteCategory.isIso_iff_bijective f).mpr
  constructor
  · intro x y hxy
    exact h.injective (congrArg g hxy)
  · intro y
    obtain ⟨x, hx⟩ := h.surjective (g y)
    exact ⟨x, hg hx⟩

theorem globalFunctions_iso_of_epi_source
    {S X Y : Scheme.{u}} (f : X ⟶ Y) [Epi f] (p : Y ⟶ S)
    [IsIso (f ≫ p).appTop] : IsIso p.appTop := by
  have he : p.appTop ≫ f.appTop = (f ≫ p).appTop := (Scheme.Hom.comp_appTop f p).symm
  have : IsIso (p.appTop ≫ f.appTop) := he.symm ▸ inferInstance
  exact isIso_left_of_isIso_comp_of_injective p.appTop f.appTop (Picard.Homomorphisms.FunctionDescent.Construction.appTop_injective_of_epi f)

def HasUniversalGlobalFunctions {S : Scheme.{u}} (A : Over S) : Prop :=
  ∀ (T : Scheme.{u}) (s : T ⟶ S), IsIso (CategoryTheory.Limits.pullback.snd A.hom s).appTop

theorem universalGlobalFunctions_of_finiteFlat_source
    {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    [IsFinite f.left] [Flat f.left] [Surjective f.left]
    (hA : HasUniversalGlobalFunctions A) : HasUniversalGlobalFunctions B := by
  intro T s
  let F := Over.pullback s
  have : IsFinite (F.map f).left := MorphismProperty.overPullbackMap (P := @IsFinite) s f inferInstance
  have : Flat (F.map f).left := MorphismProperty.overPullbackMap (P := @Flat) s f inferInstance
  have : Surjective (F.map f).left := MorphismProperty.overPullbackMap (P := @Surjective) s f inferInstance
  have : IsIso (F.obj A).hom.appTop := hA T s
  have : IsIso ((F.map f).left ≫ (F.obj B).hom).appTop := (F.map f).w.symm ▸ inferInstance
  exact globalFunctions_iso_of_epi_source (F.map f).left (F.obj B).hom

theorem fieldAbelian_hasUniversalGlobalFunctions
    {k : Type u} [Field k] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) :
    HasUniversalGlobalFunctions A.scheme := by
  intro T s
  exact A.pullback_globalFunctions_isIso s

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction
