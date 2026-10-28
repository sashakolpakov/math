import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.RelativeQuotient
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Identity Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IdentitySubgroup.Construction

noncomputable section

/-!
Over the identity parameter, the represented relative subgroup embeds in
the original abelian scheme. Its point condition is literally the given
relative subgroup, without an extra kernel-comparison hypothesis.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme (Over.mk (𝟙 S))) (R : F.Model)

def identityRelativeModelIso : (Subgroup.Construction.subgroupGroupScheme F R).X ≅ R.carrier :=
  Over.isoMk (Iso.refl _) (by
    change (𝟙 R.carrier.left) ≫ R.carrier.hom = R.toBase.left
    have h := R.toBase.w
    change R.toBase.left ≫ (𝟙 S) = R.carrier.hom at h
    exact (Category.id_comp R.carrier.hom).trans (h.symm.trans (Category.comp_id R.toBase.left)))

def identityAmbientIso : (Kernel.Inclusion.Construction.ambientGroupScheme A.scheme (Over.mk (𝟙 S))).X ≅ A.scheme :=
  AmbientComparison.Construction.ambientPullbackIso (Over.mk (𝟙 S)) A ≪≫ A.pullbackIdIso

instance identityAmbientIso_isMonHom : IsMonHom (identityAmbientIso A).hom := by
  have := AmbientComparison.Construction.ambientPullbackIso_isMonHom (Over.mk (𝟙 S)) A
  exact inferInstanceAs (IsMonHom ((AmbientComparison.Construction.ambientPullbackIso (Over.mk (𝟙 S)) A).hom ≫ A.pullbackIdIso.hom))

def identitySubgroupInclusion : (Subgroup.Construction.subgroupGroupScheme F R).X ⟶ A.scheme :=
  (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom ≫ (identityAmbientIso A).hom

instance identitySubgroupInclusion_isMonHom : IsMonHom (identitySubgroupInclusion A F R) := by
  have : IsMonHom (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom :=
    (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.isMonHom_hom
  exact inferInstanceAs (IsMonHom ((Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom ≫ (identityAmbientIso A).hom))

theorem identitySubgroupInclusion_closedImmersion :
    IsClosedImmersion (identitySubgroupInclusion A F R).left := by
  have := Kernel.Inclusion.Construction.subgroupInclusion_closedImmersion F R
  have : IsIso (identityAmbientIso A).hom.left :=
    (Over.forget S).map_isIso (identityAmbientIso A).hom
  exact inferInstanceAs (IsClosedImmersion
    ((Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom.left ≫ (identityAmbientIso A).hom.left))

theorem identitySubgroupInclusion_model :
    identitySubgroupInclusion A F R = (identityRelativeModelIso A F R).hom ≫ R.toGroup := by
  apply Over.OverMorphism.ext
  change (Kernel.Inclusion.Construction.subgroupInclusion F R).hom.hom.hom.left ≫
    ((AmbientComparison.Construction.ambientPullbackIso (Over.mk (𝟙 S)) A).hom.left ≫ A.pullbackIdIso.hom.left) =
      (𝟙 R.carrier.left) ≫ R.toGroup.left
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom_left, Kernel.Inclusion.Construction.subgroupInclusion_underlying]
  change (lift R.toBase R.toGroup).left ≫
    ((pullbackSymmetry (𝟙 S) A.scheme.hom).hom ≫ pullback.fst A.scheme.hom (𝟙 S)) = _
  rw [pullbackSymmetry_hom_comp_fst, Category.id_comp]
  exact congrArg Over.Hom.left (lift_snd R.toBase R.toGroup)

theorem identitySubgroupInclusion_points (X : Over S) (t : X ⟶ Over.mk (𝟙 S)) (a : X ⟶ A.scheme) :
    (∃! h : X ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X, h ≫ identitySubgroupInclusion A F R = a) ↔
      a ∈ F.points X t := by
  have : IsClosedImmersion (identitySubgroupInclusion A F R).left :=
    identitySubgroupInclusion_closedImmersion A F R
  have : Mono (identitySubgroupInclusion A F R) := Over.mono_of_mono_left _
  constructor
  · rintro ⟨h, hh, _⟩
    apply (R.points_iff X t a).mpr
    refine ⟨h ≫ (identityRelativeModelIso A F R).hom, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      have hb := (((h ≫ (identityRelativeModelIso A F R).hom) ≫ R.toBase).w.trans t.w.symm)
      change ((h ≫ (identityRelativeModelIso A F R).hom) ≫ R.toBase).left ≫ (𝟙 S) =
        t.left ≫ (𝟙 S) at hb
      exact (Category.comp_id _).symm.trans (hb.trans (Category.comp_id _))
    · rw [identitySubgroupInclusion_model] at hh
      simpa only [Category.assoc] using hh
  · intro ha
    obtain ⟨h, _, hh⟩ := (R.points_iff X t a).mp ha
    have hlift : (h ≫ (identityRelativeModelIso A F R).inv) ≫ identitySubgroupInclusion A F R = a := by
      simpa only [identitySubgroupInclusion_model, Category.assoc, Iso.inv_hom_id_assoc] using hh
    exact ⟨h ≫ (identityRelativeModelIso A F R).inv, hlift,
      fun y hy => (cancel_mono (identitySubgroupInclusion A F R)).mp (hy.trans hlift.symm)⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IdentitySubgroup.Construction
