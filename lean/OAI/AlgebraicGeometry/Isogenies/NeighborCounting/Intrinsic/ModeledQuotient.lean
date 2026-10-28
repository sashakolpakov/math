import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteDescent
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Action
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Markings

/-! # Modeled Quotient -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ModeledQuotient.Lifts

noncomputable section

/-! The proved FiniteDescent theorem constructs the actual native quotient over
an arbitrary base, including the non-etale integral q-primary kernels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (P : Over S)
  (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (R : F.Model) (n : ℕ)

structure NativeModeledQuotient where
  target : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g P.left
  isogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback P.hom) target
  finitePresentation : LocallyOfFinitePresentation isogeny.hom.left
  complement : target.scheme ⟶ (A.pullback P.hom).scheme
  complementGroup : IsMonHom complement
  projection_complement : isogeny.hom ≫ complement = (𝟙 (A.pullback P.hom).scheme) ^ n
  complement_projection : complement ≫ isogeny.hom = (𝟙 target.scheme) ^ n
  kernel : ∀ (T : Over P.left) (a : T ⟶ (A.pullback P.hom).scheme),
    a ≫ isogeny.hom = 1 ↔ ∃! h : T ⟶ (AbelianScheme.IsogenyQuotient.Subgroup.Construction.subgroupGroupScheme F R).X,
      h ≫ AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction.nativeSubgroupInclusion A P F R = a
  universal : AbelianScheme.IsogenyQuotient.Descent.Construction.QuotientUniversalProperty (AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction.nativeSubgroupInclusion A P F R) isogeny.hom

attribute [instance] NativeModeledQuotient.finitePresentation NativeModeledQuotient.complementGroup

def constructNativeModeledQuotient (hk : F.KilledBy n) : NativeModeledQuotient A P F R n :=
  Classical.choice (by
    let A0 := AbelianScheme.IsogenyQuotient.PELAction.Construction.abelianSchemeForgetDimension A
    obtain ⟨B0, f0, g0, hg0, hfg0, hgf0, hker0, hUP0⟩ :=
      AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.quotient_isogeny_and_complement_of_FiniteDescent A0 P F R n hk FiniteDescent.Lifts.verified_FiniteDescentInput
    have : IsMonHom g0 := hg0
    have : IsMonHom f0.hom := f0.isMonHom
    have : IsFinite f0.hom.left := f0.finite
    have : Flat f0.hom.left := f0.flat
    have : Surjective f0.hom.left := f0.surjective
    have : LocallyOfFinitePresentation f0.hom.left := f0.finitePresentation
    let e : (AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.baseChangedAbelianScheme A0 P).toOver ≅ (A.pullback P.hom).scheme :=
      AbelianScheme.IsogenyQuotient.AmbientComparison.Construction.ambientPullbackIso P A
    have : IsMonHom e.hom := AbelianScheme.IsogenyQuotient.AmbientComparison.Construction.ambientPullbackIso_isMonHom P A
    have : IsMonHom e.inv := inferInstance
    have : IsIso e.inv.left := (Over.forget P.left).map_isIso e.inv
    let fraw : (A.pullback P.hom).scheme ⟶ B0.toOver := e.inv ≫ f0.hom
    have hrawGroup : IsMonHom fraw := inferInstanceAs (IsMonHom (e.inv ≫ f0.hom))
    have hrawFinite : IsFinite fraw.left := inferInstanceAs (IsFinite (e.inv.left ≫ f0.hom.left))
    have hrawFlat : Flat fraw.left := inferInstanceAs (Flat (e.inv.left ≫ f0.hom.left))
    have hrawSurjective : Surjective fraw.left := inferInstanceAs (Surjective (e.inv.left ≫ f0.hom.left))
    have : LocallyOfFinitePresentation fraw.left :=
      inferInstanceAs (LocallyOfFinitePresentation (e.inv.left ≫ f0.hom.left))
    let B := AbelianScheme.IsogenyQuotient.Dimension.Construction.abelianQuotientWithDimension (A.pullback P.hom) B0 fraw
    let f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback P.hom) B := {
      hom := fraw
      preservesGroup := hrawGroup
      finite := hrawFinite
      flat := hrawFlat
      surjective := hrawSurjective }
    let c : B.scheme ⟶ (A.pullback P.hom).scheme := g0 ≫ e.hom
    have hc : IsMonHom c := inferInstanceAs (IsMonHom (g0 ≫ e.hom))
    refine ⟨⟨B, f, inferInstanceAs (LocallyOfFinitePresentation fraw.left), c, hc, ?_, ?_, ?_, ?_⟩⟩
    · change (e.inv ≫ f0.hom) ≫ (g0 ≫ e.hom) = _
      rw [Category.assoc, ← Category.assoc f0.hom, hfg0,
        MonObj.pow_comp, Category.id_comp, MonObj.comp_pow, e.inv_hom_id]
    · change (g0 ≫ e.hom) ≫ (e.inv ≫ f0.hom) = _
      rw [Category.assoc, e.hom_inv_id_assoc, hgf0]
      rfl
    · exact AbelianScheme.IsogenyQuotient.Intrinsic.RelativeQuotient.Construction.kernel_property_precompose_iso e (AbelianScheme.IsogenyQuotient.Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom f0.hom hker0
    · exact AbelianScheme.IsogenyQuotient.Intrinsic.RelativeQuotient.Construction.quotient_property_precompose_iso e (AbelianScheme.IsogenyQuotient.Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom f0.hom hUP0)

variable {A P F R n} (Q : NativeModeledQuotient A P F R n)

def NativeModeledQuotient.action {O : Type v} [CommRing O]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (hstable : ∀ a, AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable F (ρ.map a)) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction O Q.target :=
  (AbelianScheme.IsogenyQuotient.Intrinsic.Action.Construction.native_quotient_integral_action A P F R Q.target Q.isogeny Q.kernel Q.universal ρ hstable).choose

theorem NativeModeledQuotient.action_projection {O : Type v} [CommRing O]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (hstable : ∀ a, AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable F (ρ.map a)) (a : O) :
    Q.isogeny.hom ≫ (Q.action ρ hstable).map a = (ρ.pullback P.hom).map a ≫ Q.isogeny.hom :=
  (AbelianScheme.IsogenyQuotient.Intrinsic.Action.Construction.native_quotient_integral_action A P F R Q.target Q.isogeny Q.kernel Q.universal ρ hstable).choose_spec.1 a

def NativeModeledQuotient.level (N : ℕ) (hcop : n.Coprime N)
    (level : (A.pullback P.hom).FullLevel N) : Q.target.FullLevel N :=
  AbelianScheme.IsogenyQuotient.Markings.Construction.transportFullLevel (A.pullback P.hom) Q.target Q.isogeny.hom Q.complement n N hcop
    Q.projection_complement Q.complement_projection level

theorem NativeModeledQuotient.level_projection (N : ℕ) (hcop : n.Coprime N)
    (level : (A.pullback P.hom).FullLevel N) (T : Over P.left)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    ((Q.level N hcop level).hom.app (.op T) c).val =
      (level.hom.app (.op T) c).val ≫ Q.isogeny.hom :=
  AbelianScheme.IsogenyQuotient.Markings.Construction.transportFullLevel_apply (A.pullback P.hom) Q.target Q.isogeny.hom Q.complement n N hcop
    Q.projection_complement Q.complement_projection level T c

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ModeledQuotient.Lifts
