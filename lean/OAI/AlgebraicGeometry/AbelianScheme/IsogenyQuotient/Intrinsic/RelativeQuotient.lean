import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AmbientComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Dimension
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Etale

/-! # Relative Quotient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.RelativeQuotient.Construction

noncomputable section

/-!
The quotient construction on ReferenceFamily's standard pulled-back abelian scheme.
The canonical ambient comparison transfers the exact kernel, quotient
universal property, and complementary multiplication identities. The
quotient's fixed relative dimension is derived, not supplied.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

section IsoTransport

variable {C : Type*} [Category.{v} C] [CartesianMonoidalCategory C]
  {A A' B H : C} [GrpObj A] [GrpObj A'] [GrpObj B]

omit [GrpObj A] [GrpObj A'] in
theorem kernel_property_precompose_iso
    (e : A ≅ A') (i : H ⟶ A) (f : A ⟶ B)
    (hker : ∀ (T : C) (a : T ⟶ A), a ≫ f = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a) :
    ∀ (T : C) (a : T ⟶ A'),
      a ≫ (e.inv ≫ f) = 1 ↔ ∃! h : T ⟶ H, h ≫ (i ≫ e.hom) = a := by
  intro T a
  rw [← Category.assoc, hker]
  apply existsUnique_congr
  intro h
  constructor
  · intro hh
    rw [← Category.assoc, hh, Category.assoc, e.inv_hom_id, Category.comp_id]
  · intro hh
    have h := congrArg (fun z => z ≫ e.inv) hh
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using h

omit [GrpObj B] in
theorem quotient_property_precompose_iso
    (e : A ≅ A') [IsMonHom e.hom] (i : H ⟶ A) (f : A ⟶ B)
    (hUP : Descent.Construction.QuotientUniversalProperty i f) :
    Descent.Construction.QuotientUniversalProperty (i ≫ e.hom) (e.inv ≫ f) := by
  intro T g hg
  have hinv : ∀ (U : C) (a : U ⟶ A) (h : U ⟶ H),
      ((h ≫ i) * a) ≫ (e.hom ≫ g) = a ≫ (e.hom ≫ g) := by
    intro U a h
    simpa only [← Category.assoc, MonObj.mul_comp] using hg U (a ≫ e.hom) h
  obtain ⟨d, hd, hu⟩ := hUP T (e.hom ≫ g) hinv
  refine ⟨d, ?_, ?_⟩
  · change (e.inv ≫ f) ≫ d = g
    rw [Category.assoc, hd, e.inv_hom_id_assoc]
  · intro d' hd'
    apply hu d'
    have h := congrArg (fun z => e.hom ≫ z) hd'
    simpa only [← Category.assoc, e.hom_inv_id, Category.id_comp] using h

end IsoTransport

set_option backward.isDefEq.respectTransparency false in
/-- TorsionQuotient and FiniteDescent construct the finite-etale quotient of the actual ReferenceFamily
pullback family. The target carries the same proved relative dimension. -/
theorem native_relative_quotient_from_TorsionQuotient_FiniteDescent
    {S : Scheme.{u}} {dim : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dim S) (P : Over S)
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (R : F.Model)
    (n : ℕ) (hkilled : F.KilledBy n)
    (h_TorsionQuotient : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A.scheme n).hom)
    (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{u}) :
    ∃ (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dim P.left) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback P.hom) B)
      (g : B.scheme ⟶ (A.pullback P.hom).scheme),
      Etale f.hom.left ∧ IsMonHom g ∧
      f.hom ≫ g = (𝟙 (A.pullback P.hom).scheme) ^ n ∧
      g ≫ f.hom = (𝟙 B.scheme) ^ n ∧
      (∀ (T : Over P.left) (a : T ⟶ (A.pullback P.hom).scheme),
        a ≫ f.hom = 1 ↔ ∃! h : T ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
          h ≫ ((Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom ≫ (AmbientComparison.Construction.ambientPullbackIso P A).hom) = a) ∧
      Descent.Construction.QuotientUniversalProperty
        ((Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom ≫ (AmbientComparison.Construction.ambientPullbackIso P A).hom) f.hom := by
  let A0 := PELAction.Construction.abelianSchemeForgetDimension A
  obtain ⟨B0, f0, g0, hg0, hfg0, hgf0, hker0, hUP0⟩ :=
    IsogenyComplement.Construction.quotient_isogeny_and_complement_of_FiniteDescent A0 P F R n hkilled h_FiniteDescent
  have : IsMonHom g0 := hg0
  have hf0etale : Etale f0.hom.left :=
    IsogenyQuotient.Etale.Construction.constructed_quotient_etale A0 P F R n hkilled h_TorsionQuotient B0 f0 hker0
  have : Etale f0.hom.left := hf0etale
  let e := AmbientComparison.Construction.ambientPullbackIso P A
  have : IsMonHom e.hom := AmbientComparison.Construction.ambientPullbackIso_isMonHom P A
  have : IsMonHom e.inv := inferInstance
  have : IsIso e.inv.left := (Over.forget P.left).map_isIso e.inv
  let q : (A.pullback P.hom).scheme ⟶ B0.toOver := e.inv ≫ f0.hom
  have : IsMonHom q := inferInstanceAs (IsMonHom (e.inv ≫ f0.hom))
  have : IsFinite q.left := inferInstanceAs (IsFinite (e.inv.left ≫ f0.hom.left))
  have : Flat q.left := inferInstanceAs (Flat (e.inv.left ≫ f0.hom.left))
  have : Surjective q.left := inferInstanceAs (Surjective (e.inv.left ≫ f0.hom.left))
  have : Etale q.left := inferInstanceAs (Etale (e.inv.left ≫ f0.hom.left))
  let B := Dimension.Construction.abelianQuotientWithDimension (A.pullback P.hom) B0 q
  let f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback P.hom) B := {
    hom := q
    preservesGroup := inferInstance
    finite := inferInstance
    flat := inferInstance
    surjective := inferInstance }
  let g : B.scheme ⟶ (A.pullback P.hom).scheme := g0 ≫ e.hom
  have hg : IsMonHom g := inferInstanceAs (IsMonHom (g0 ≫ e.hom))
  refine ⟨B, f, g, inferInstanceAs (Etale q.left), hg, ?_, ?_, ?_, ?_⟩
  · change (e.inv ≫ f0.hom) ≫ (g0 ≫ e.hom) = _
    rw [Category.assoc, ← Category.assoc f0.hom, hfg0,
      MonObj.pow_comp, Category.id_comp, MonObj.comp_pow, e.inv_hom_id]
  · change (g0 ≫ e.hom) ≫ (e.inv ≫ f0.hom) = _
    rw [Category.assoc, e.hom_inv_id_assoc, hgf0]
    rfl
  · exact kernel_property_precompose_iso e (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom f0.hom hker0
  · exact quotient_property_precompose_iso e (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom f0.hom hUP0

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.RelativeQuotient.Construction
