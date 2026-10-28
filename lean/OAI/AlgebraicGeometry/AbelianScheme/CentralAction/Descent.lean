import Mathlib

/-! # Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Descent.Construction

noncomputable section

/-! Geometric descent tools for the scalar comparison in CentralAction. Equal
scheme-theoretic kernels give actual quotient isomorphisms. Complementary
endomorphisms of a finite etale surjection are finite etale surjections.
No statement about finite order of a correspondence is an assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

section Quotients

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A B Z : C} [GrpObj A] [GrpObj B] [GrpObj Z]

theorem kernel_inclusion_coequalizes
    (f : A ⟶ B) [IsMonHom f] (g : A ⟶ Z) [IsMonHom g]
    (hker : ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 → x ≫ g = 1)
    {T : C} (x y : T ⟶ A) (hxy : x ≫ f = y ≫ f) :
    x ≫ g = y ≫ g := by
  have hk : (x / y) ≫ f = 1 := by rw [GrpObj.div_comp, hxy, div_self']
  have hd := hker T (x / y) hk
  rwa [GrpObj.div_comp, div_eq_one] at hd

/-- Canonical isomorphism between two effective group quotients with
the same kernel on all test objects, including nonreduced tests. -/
def equalKernelQuotientIso
    (f : A ⟶ B) [IsMonHom f] [EffectiveEpi f]
    (g : A ⟶ Z) [IsMonHom g] [EffectiveEpi g]
    (hker : ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 ↔ x ≫ g = 1) : B ≅ Z where
  hom := EffectiveEpi.desc f g (kernel_inclusion_coequalizes f g (fun T x => (hker T x).mp))
  inv := EffectiveEpi.desc g f (kernel_inclusion_coequalizes g f (fun T x => (hker T x).mpr))
  hom_inv_id := by
    apply (cancel_epi f).mp
    rw [← Category.assoc, EffectiveEpi.fac, EffectiveEpi.fac, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi g).mp
    rw [← Category.assoc, EffectiveEpi.fac, EffectiveEpi.fac, Category.comp_id]

theorem equalKernelQuotientIso_fac
    (f : A ⟶ B) [IsMonHom f] [EffectiveEpi f]
    (g : A ⟶ Z) [IsMonHom g] [EffectiveEpi g]
    (hker : ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 ↔ x ≫ g = 1) :
    f ≫ (equalKernelQuotientIso f g hker).hom = g :=
  EffectiveEpi.fac f g (kernel_inclusion_coequalizes f g (fun T x => (hker T x).mp))

end Quotients

/-- The usual cancellation properties of finite and etale morphisms
construct the needed scalar-isogeny geometry from a complementary scalar. -/
theorem finite_etale_surjective_of_complements
    {X : Scheme} (f g p : X ⟶ X)
    (hfg : f ≫ g = p) (hgf : g ≫ f = p)
    [IsSeparated f] [IsSeparated g] [IsFinite p] [Etale p] [Surjective p] :
    IsFinite f ∧ Etale f ∧ Surjective f := by
  have hfgFinite : IsFinite (f ≫ g) := hfg ▸ inferInstance
  have hgfFinite : IsFinite (g ≫ f) := hgf ▸ inferInstance
  have hfFinite : IsFinite f := IsFinite.of_comp f g
  have hgFinite : IsFinite g := IsFinite.of_comp g f
  have hfgEtale : Etale (f ≫ g) := hfg ▸ inferInstance
  have hgfEtale : Etale (g ≫ f) := hgf ▸ inferInstance
  have hgUnramified : FormallyUnramified g := FormallyUnramified.of_comp g f
  have hfEtale : Etale f := Etale.of_comp f g
  refine ⟨hfFinite, hfEtale, ⟨?_⟩⟩
  intro x
  obtain ⟨y, hy⟩ := p.surjective x
  refine ⟨g y, ?_⟩
  change (g ≫ f) y = x
  rw [hgf]
  exact hy

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Descent.Construction
