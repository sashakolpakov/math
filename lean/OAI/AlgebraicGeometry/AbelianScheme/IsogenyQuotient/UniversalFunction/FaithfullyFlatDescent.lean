import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsMapRigidity
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Faithfully Flat Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Universal global functions descend along faithfully flat changes
of the base for pointed families. No finite-presentation or Noetherian
condition is imposed on the covering morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsMapRigidity

universe u

set_option backward.isDefEq.respectTransparency false in
theorem UniversalFunction.FaithfullyFlatDescent.Construction.globalFunctions_isIso_of_faithfullyFlat_baseChange
    {S T X : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (u : T ⟶ S) [Flat u] [Surjective u]
    [IsIso (pullback.snd f u).appTop] : IsIso f.appTop := by
  let p := pullback.snd f u
  let a := pullback.fst f u
  have : Epi a := Flat.epi_of_flat_of_surjective (pullback.fst f u)
  let τ : T ⟶ pullback f u := pullback.lift (u ≫ σ) (𝟙 T) (by simp [Category.assoc, hσ])
  have hτ : τ ≫ p = 𝟙 T := pullback.lift_snd _ _ _
  have hm : X.toSpecΓ = f ≫ σ ≫ X.toSpecΓ := by
    apply (cancel_epi a).mp
    have h := AbelianModuli.HilbertConstruction.Global.FunctionsMapRigidity.affineMap_eq_of_globalFunctions_iso p τ hτ (a ≫ X.toSpecΓ)
    calc
      a ≫ X.toSpecΓ = p ≫ τ ≫ a ≫ X.toSpecΓ := h
      _ = p ≫ u ≫ σ ≫ X.toSpecΓ := by simp [τ, a, Category.assoc]
      _ = a ≫ f ≫ σ ≫ X.toSpecΓ := by rw [← Category.assoc p u, ← pullback.condition]; simp [Category.assoc, a]
  have h := congrArg Scheme.Hom.appTop hm
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
  have he : σ.appTop ≫ f.appTop = 𝟙 Γ(X, ⊤) := by
    apply (cancel_epi (Scheme.ΓSpecIso Γ(X, ⊤)).hom).mp
    simpa only [Category.comp_id, Category.assoc] using h.symm
  exact (show Γ(S, ⊤) ≅ Γ(X, ⊤) from {
    hom := f.appTop
    inv := σ.appTop
    hom_inv_id := by rw [← Scheme.Hom.comp_appTop, hσ, Scheme.Hom.id_appTop]
    inv_hom_id := he }).isIso_hom

set_option backward.isDefEq.respectTransparency false in
theorem GlobalFunctions.Construction.HasUniversalGlobalFunctions.of_faithfullyFlat_baseChange
    {S T : Scheme.{u}} {A : Over S} (σ : S ⟶ A.left) (hσ : σ ≫ A.hom = 𝟙 S)
    (u : T ⟶ S) [Flat u] [Surjective u]
    (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions ((Over.pullback u).obj A)) :
    GlobalFunctions.Construction.HasUniversalGlobalFunctions A := by
  intro U b
  let f := pullback.snd A.hom b
  let v := pullback.fst b u
  let w := pullback.snd b u
  let a := pullback.fst f v ≫ pullback.fst A.hom b
  let p := pullback.snd f v
  have hp : IsPullback a p A.hom (v ≫ b) :=
    (IsPullback.of_hasPullback f v).paste_horiz (IsPullback.of_hasPullback A.hom b)
  have he : v ≫ b = w ≫ u := pullback.condition
  have hp' : IsPullback a p A.hom (w ≫ u) := he ▸ hp
  have hlocal : IsIso p.appTop :=
    hA.isIso_of_isPullback _ p w (hp'.of_right' (IsPullback.of_hasPullback A.hom u))
  let τ : U ⟶ Limits.pullback A.hom b :=
    pullback.lift (b ≫ σ) (𝟙 U) (by simp [Category.assoc, hσ])
  exact UniversalFunction.FaithfullyFlatDescent.Construction.globalFunctions_isIso_of_faithfullyFlat_baseChange f τ (pullback.lift_snd _ _ _) v

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
