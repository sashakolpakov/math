import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedFamilyPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

/-! # Rigidified Heterogeneous Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedHeterogeneousPullback

noncomputable section

/-! Native pullback of a normalized comparison between line objects
on different parameter schemes, retaining both original zero frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

private def heterogeneousCompositeIso {X₁ X₂ Y Z : Scheme.{u}}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (j : Z ⟶ Y) (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (e : (Scheme.Modules.pullback f₁).obj M₁ ≅ (Scheme.Modules.pullback f₂).obj M₂) :
    (Scheme.Modules.pullback (j ≫ f₁)).obj M₁ ≅ (Scheme.Modules.pullback (j ≫ f₂)).obj M₂ :=
  (Scheme.Modules.pullbackComp j f₁).symm.app M₁ ≪≫
    (Scheme.Modules.pullback j).mapIso e ≪≫ (Scheme.Modules.pullbackComp j f₂).app M₂

private theorem heterogeneousCompositeIso_normalized
    {X₁ X₂ Y Z S₁ S₂ T U : Scheme.{u}} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (j : Z ⟶ Y)
    (s₁ : S₁ ⟶ X₁) (s₂ : S₂ ⟶ X₂) (b : T ⟶ Y) (g₁ : T ⟶ S₁) (g₂ : T ⟶ S₂)
    (c : U ⟶ Z) (t : U ⟶ T)
    (h : c ≫ j = t ≫ b) (h₁ : b ≫ f₁ = g₁ ≫ s₁) (h₂ : b ≫ f₂ = g₂ ≫ s₂)
    (h₁' : c ≫ (j ≫ f₁) = (t ≫ g₁) ≫ s₁) (h₂' : c ≫ (j ≫ f₂) = (t ≫ g₂) ≫ s₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (r₁ : (Scheme.Modules.pullback s₁).obj M₁ ≅ Line.Bundles.structureModule S₁)
    (r₂ : (Scheme.Modules.pullback s₂).obj M₂ ≅ Line.Bundles.structureModule S₂)
    (e : (Scheme.Modules.pullback f₁).obj M₁ ≅ (Scheme.Modules.pullback f₂).obj M₂)
    (he : (Scheme.Modules.pullback b).map e.hom ≫
      (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f₂ b g₂ s₂ h₂ M₂ r₂).hom =
        (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f₁ b g₁ s₁ h₁ M₁ r₁).hom) :
    (Scheme.Modules.pullback c).map (heterogeneousCompositeIso f₁ f₂ j M₁ M₂ e).hom ≫
      (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso (j ≫ f₂) c (t ≫ g₂) s₂ h₂' M₂ r₂).hom =
        (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso (j ≫ f₁) c (t ≫ g₁) s₁ h₁' M₁ r₁).hom := by
  apply (cancel_epi ((Scheme.Modules.pullback c).map ((Scheme.Modules.pullbackComp j f₁).hom.app M₁))).mp
  simp only [heterogeneousCompositeIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, (Scheme.Modules.pullback c).map_id, Category.id_comp]
  rw [FormalGeometry.Completion.RigidificationComparisonPasting.Construction.rigidificationBaseChangeIso_paste f₂ j s₂ b g₂ c t h h₂ h₂' M₂ r₂,
    FormalGeometry.Completion.RigidificationComparisonPasting.Construction.rigidificationBaseChangeIso_paste f₁ j s₁ b g₁ c t h h₁ h₁' M₁ r₁,
    FormalGeometry.Completion.Rigidified.IsoPullback.Construction.pullbackSquare_naturality_assoc]
  rw [← Functor.map_comp_assoc, he]

private theorem heterogeneousPullback_normalized
    {X₁ X₂ Y Z S₁ S₂ T U : Scheme.{u}} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (j : Z ⟶ Y)
    (f₁' : Z ⟶ X₁) (f₂' : Z ⟶ X₂) (hj₁ : j ≫ f₁ = f₁') (hj₂ : j ≫ f₂ = f₂')
    (s₁ : S₁ ⟶ X₁) (s₂ : S₂ ⟶ X₂) (b : T ⟶ Y) (g₁ : T ⟶ S₁) (g₂ : T ⟶ S₂)
    (c : U ⟶ Z) (t : U ⟶ T)
    (h : c ≫ j = t ≫ b) (h₁ : b ≫ f₁ = g₁ ≫ s₁) (h₂ : b ≫ f₂ = g₂ ≫ s₂)
    (h₁' : c ≫ f₁' = (t ≫ g₁) ≫ s₁) (h₂' : c ≫ f₂' = (t ≫ g₂) ≫ s₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (r₁ : (Scheme.Modules.pullback s₁).obj M₁ ≅ Line.Bundles.structureModule S₁)
    (r₂ : (Scheme.Modules.pullback s₂).obj M₂ ≅ Line.Bundles.structureModule S₂)
    (e : (Scheme.Modules.pullback f₁).obj M₁ ≅ (Scheme.Modules.pullback f₂).obj M₂)
    (he : (Scheme.Modules.pullback b).map e.hom ≫
      (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f₂ b g₂ s₂ h₂ M₂ r₂).hom =
        (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f₁ b g₁ s₁ h₁ M₁ r₁).hom) :
    (Scheme.Modules.pullback c).map
        (Picard.PoincareBundle.PullbackFiberComposition.pullIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks e j f₁' f₂' hj₁ hj₂).hom ≫
      (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f₂' c (t ≫ g₂) s₂ h₂' M₂ r₂).hom =
        (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso f₁' c (t ≫ g₁) s₁ h₁' M₁ r₁).hom := by
  change (Scheme.Modules.pullback c).map
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks) e.hom j f₁' f₂' hj₁ hj₂) ≫ _ = _
  rw [Picard.PoincareBundle.Geometric.PullHom.pullHom_eq]
  subst f₁'
  subst f₂'
  have hn := heterogeneousCompositeIso_normalized
    f₁ f₂ j s₁ s₂ b g₁ g₂ c t h h₁ h₂ h₁' h₂' M₁ M₂ r₁ r₂ e he
  change (Scheme.Modules.pullback c).map
      ((Scheme.Modules.pullbackComp j f₁).inv.app M₁ ≫
        (Scheme.Modules.pullback j).map e.hom ≫ (Scheme.Modules.pullbackComp j f₂).hom.app M₂) ≫
      (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso (j ≫ f₂) c (t ≫ g₂) s₂ h₂' M₂ r₂).hom =
        (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso (j ≫ f₁) c (t ≫ g₁) s₁ h₁' M₁ r₁).hom at hn
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl]
  change (Scheme.Modules.pullback c).map
      ((Scheme.Modules.pullbackComp j f₁).inv.app M₁ ≫
        (Scheme.Modules.pullback j).map e.hom ≫ (Scheme.Modules.pullbackComp j f₂).hom.app M₂) ≫
      (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso (j ≫ f₂) c (t ≫ g₂) s₂ h₂' M₂ r₂).hom =
        (FormalGeometry.Completion.Rigidified.FrameScalar.Construction.rigidificationBaseChangeIso (j ≫ f₁) c (t ≫ g₁) s₁ h₁' M₁ r₁).hom
  exact hn

private theorem modulePullIso_hom
    {X₁ X₂ Y Z : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (Scheme.Modules.pullback f₁).obj M₁ ≅ (Scheme.Modules.pullback f₂).obj M₂)
    (j : Z ⟶ Y) (f₁' : Z ⟶ X₁) (f₂' : Z ⟶ X₂)
    (h₁ : j ≫ f₁ = f₁') (h₂ : j ≫ f₂ = f₂') :
    (Picard.PoincareBundle.PullbackFiberComposition.pullIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks (A := X₁) (B := X₂) (T := Y) (T' := Z)
      (M := M₁) (N := M₂) (x := f₁) (y := f₂) e j f₁' f₂' h₁ h₂).hom =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks)
        (X₁ := X₁) (X₂ := X₂) (M₁ := M₁) (M₂ := M₂)
        (Y := Y) (Y' := Z) (f₁ := f₁) (f₂ := f₂) e.hom j f₁' f₂' h₁ h₂ := rfl

private theorem iso_hom_congr {C : Type*} [Category* C] {X Y : C}
    {e f : X ≅ Y} (h : e = f) : e.hom = f.hom :=
  congrArg (fun q : X ≅ Y => q.hom) h

namespace RigidifiedLineBundleIso
variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) {T U V W : Over S}

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedLineBundles.RigidifiedLineBundleIso.nativeFamilyPullbackTo
    {L : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left}
    {M : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A W).left}
    (a : T ⟶ V) (b : T ⟶ W)
    (e : RigidifiedLineBundles.RigidifiedLineBundleIso (L.familyPullback A a) (M.familyPullback A b))
    (t : U ⟶ T) (a' : U ⟶ V) (b' : U ⟶ W)
    (ha : t ≫ a = a') (hb : t ≫ b = b') :
    RigidifiedLineBundles.RigidifiedLineBundleIso (L.familyPullback A a') (M.familyPullback A b') where
  underlying := Picard.PoincareBundle.PullbackFiberComposition.pullIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks e.underlying (t ▷ A.scheme).left
    (a' ▷ A.scheme).left (b' ▷ A.scheme).left
    (congrArg Over.Hom.left ((comp_whiskerRight t a A.scheme).symm.trans
      (congrArg (fun x => x ▷ A.scheme) ha)))
    (congrArg Over.Hom.left ((comp_whiskerRight t b A.scheme).symm.trans
      (congrArg (fun x => x ▷ A.scheme) hb)))
  normalized := by
    subst a'
    subst b'
    exact heterogeneousPullback_normalized (a ▷ A.scheme).left (b ▷ A.scheme).left
      (t ▷ A.scheme).left ((t ≫ a) ▷ A.scheme).left ((t ≫ b) ▷ A.scheme).left _ _
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A W).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left a.left b.left
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero A U).left t.left
      (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A t))
      (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A a))
      (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A b))
      (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A (t ≫ a)))
      (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A (t ≫ b)))
      L.lineBundle.sheaf M.lineBundle.sheaf L.rigidification M.rigidification e.underlying e.normalized

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedLineBundles.RigidifiedLineBundleIso.nativeFamilyPullbackTo_underlying
    {L : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left}
    {M : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A W).left}
    (a : T ⟶ V) (b : T ⟶ W)
    (e : RigidifiedLineBundles.RigidifiedLineBundleIso (L.familyPullback A a) (M.familyPullback A b))
    (t : U ⟶ T) (a' : U ⟶ V) (b' : U ⟶ W)
    (ha : t ≫ a = a') (hb : t ≫ b = b') :
    (RigidifiedLineBundles.RigidifiedLineBundleIso.nativeFamilyPullbackTo A a b e t a' b' ha hb).underlying =
      Picard.PoincareBundle.PullbackFiberComposition.pullIso Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks
        (A := (V ⊗ A.scheme).left) (B := (W ⊗ A.scheme).left)
        (T := (T ⊗ A.scheme).left) (T' := (U ⊗ A.scheme).left)
        (M := L.lineBundle.sheaf) (N := M.lineBundle.sheaf)
        (x := (a ▷ A.scheme).left) (y := (b ▷ A.scheme).left) e.underlying
        (t ▷ A.scheme).left (a' ▷ A.scheme).left (b' ▷ A.scheme).left
        (congrArg Over.Hom.left ((comp_whiskerRight t a A.scheme).symm.trans
          (congrArg (fun f => f ▷ A.scheme) ha)))
        (congrArg Over.Hom.left ((comp_whiskerRight t b A.scheme).symm.trans
          (congrArg (fun f => f ▷ A.scheme) hb))) := rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedLineBundles.RigidifiedLineBundleIso.nativeFamilyPullbackTo_hom
    {L : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left}
    {M : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A W).left}
    (a : T ⟶ V) (b : T ⟶ W)
    (e : RigidifiedLineBundles.RigidifiedLineBundleIso (L.familyPullback A a) (M.familyPullback A b))
    (t : U ⟶ T) (a' : U ⟶ V) (b' : U ⟶ W)
    (ha : t ≫ a = a') (hb : t ≫ b = b') :
    (RigidifiedLineBundles.RigidifiedLineBundleIso.nativeFamilyPullbackTo A a b e t a' b' ha hb).underlying.hom =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks)
        (X₁ := (V ⊗ A.scheme).left) (X₂ := (W ⊗ A.scheme).left)
        (M₁ := L.lineBundle.sheaf) (M₂ := M.lineBundle.sheaf)
        (f₁ := (a ▷ A.scheme).left) (f₂ := (b ▷ A.scheme).left) e.underlying.hom
        (t ▷ A.scheme).left (a' ▷ A.scheme).left (b' ▷ A.scheme).left
        (congrArg Over.Hom.left ((comp_whiskerRight t a A.scheme).symm.trans
          (congrArg (fun f => f ▷ A.scheme) ha)))
        (congrArg Over.Hom.left ((comp_whiskerRight t b A.scheme).symm.trans
          (congrArg (fun f => f ▷ A.scheme) hb))) := by
  have h₁ := RigidifiedLineBundles.RigidifiedLineBundleIso.nativeFamilyPullbackTo_underlying A a b e t a' b' ha hb
  have h₂ := modulePullIso_hom
    (X₁ := (V ⊗ A.scheme).left) (X₂ := (W ⊗ A.scheme).left)
    (Y := (T ⊗ A.scheme).left) (Z := (U ⊗ A.scheme).left)
    (M₁ := L.lineBundle.sheaf) (M₂ := M.lineBundle.sheaf)
    (f₁ := (a ▷ A.scheme).left) (f₂ := (b ▷ A.scheme).left) e.underlying
    (t ▷ A.scheme).left (a' ▷ A.scheme).left (b' ▷ A.scheme).left
    (congrArg Over.Hom.left ((comp_whiskerRight t a A.scheme).symm.trans
      (congrArg (fun f => f ▷ A.scheme) ha)))
    (congrArg Over.Hom.left ((comp_whiskerRight t b A.scheme).symm.trans
      (congrArg (fun f => f ▷ A.scheme) hb)))
  exact (iso_hom_congr h₁).trans h₂

end RigidifiedLineBundleIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedHeterogeneousPullback
