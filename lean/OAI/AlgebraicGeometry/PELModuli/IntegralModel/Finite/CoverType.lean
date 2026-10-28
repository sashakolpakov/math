import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FunctionDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Adjoin.Tower

/-! # Cover Type -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverType

noncomputable section

section

/-! Finite flat surjective covers descend finite type over a noetherian
base. The affine argument is the actual Artin--Tate lemma on sections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem finite_flat_affine_cover_finiteType {X Y S : Scheme.{0}}
    [IsAffine Y] [IsAffine S] [IsLocallyNoetherian S]
    (f : X ⟶ Y) (p : Y ⟶ S) [IsFinite f] [Flat f] [Surjective f]
    [LocallyOfFiniteType (f ≫ p)] : LocallyOfFiniteType p := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  have hfin : f.appTop.hom.Finite :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := f)).mp inferInstance).2
  have hcomp : (f.appTop.hom.comp p.appTop.hom).FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := f ≫ p)).mp inferInstance
  have : Epi f := Flat.epi_of_flat_of_surjective f
  have hi : Function.Injective f.appTop.hom := Isogenies.NeighborCounting.FunctionDescent.appTop_injective_of_epi f
  let : Algebra Γ(S, ⊤) Γ(Y, ⊤) := p.appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop.hom.comp p.appTop.hom).toAlgebra
  have : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := hfin
  have : Algebra.FiniteType Γ(S, ⊤) Γ(X, ⊤) := hcomp
  have h : Algebra.FiniteType Γ(S, ⊤) Γ(Y, ⊤) :=
    ⟨fg_of_fg_of_fg Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) Algebra.FiniteType.out
      (Module.Finite.fg_top (R := Γ(Y, ⊤)) (M := Γ(X, ⊤))) hi⟩
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := p)).mpr h

theorem finite_flat_cover_finiteType {X Y S : Scheme.{0}}
    [IsAffine S] [IsLocallyNoetherian S]
    (f : X ⟶ Y) (p : Y ⟶ S) [IsFinite f] [Flat f] [Surjective f]
    [LocallyOfFiniteType (f ≫ p)] : LocallyOfFiniteType p := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover).mpr
  intro i
  let q := CategoryTheory.Limits.pullback.snd f (Y.affineCover.f i)
  have hcomp : q ≫ (Y.affineCover.f i ≫ p) =
      CategoryTheory.Limits.pullback.fst f (Y.affineCover.f i) ≫ (f ≫ p) := by
    change CategoryTheory.Limits.pullback.snd f (Y.affineCover.f i) ≫ (Y.affineCover.f i ≫ p) = _
    rw [← Category.assoc, ← CategoryTheory.Limits.pullback.condition, Category.assoc]
  have : LocallyOfFiniteType (q ≫ (Y.affineCover.f i ≫ p)) := by
    rw [hcomp]
    infer_instance
  exact finite_flat_affine_cover_finiteType q (Y.affineCover.f i ≫ p)

theorem quasiCompact_of_surjective_comp {X Y S : Scheme.{0}} (f : X ⟶ Y) (p : Y ⟶ S)
    [Surjective f] [QuasiCompact (f ≫ p)] : QuasiCompact p := by
  constructor
  intro U ho hc
  have h := (QuasiCompact.isCompact_preimage (f := f ≫ p) U ho hc).image f.continuous
  convert h using 1
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := (inferInstance : Surjective f).surj y
    exact ⟨x, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

end

/-! A finite flat surjective cover of finite type proves that the
target is an actual noetherian finite-type parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem finite_flat_cover_noetherian
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {V X : Over (Spec (.of R))} (f : V ⟶ X)
    [IsFinite f.left] [Flat f.left] [Surjective f.left]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] :
    LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom ∧ IsNoetherian X.left := by
  have : LocallyOfFiniteType (f.left ≫ X.hom) := f.w.symm ▸ inferInstanceAs (LocallyOfFiniteType V.hom)
  have : QuasiCompact (f.left ≫ X.hom) := f.w.symm ▸ inferInstanceAs (QuasiCompact V.hom)
  have : LocallyOfFiniteType X.hom := finite_flat_cover_finiteType f.left X.hom
  have : QuasiCompact X.hom := quasiCompact_of_surjective_comp f.left X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact ⟨inferInstance, inferInstance, ⟨⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.CoverType
