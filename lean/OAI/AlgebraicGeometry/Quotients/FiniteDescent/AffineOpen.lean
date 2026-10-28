import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSquare
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenPullbackId

/-! # Affine Open -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineOpen

noncomputable section

/-! Affine base change for sections on affine opens of the source scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

universe u

namespace Construction.AffineOpenSquare

variable {X Y S T : Scheme.{u}} [IsAffine S] [IsAffine T]
variable (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : IsPullback f ρ π g) (M : X.Modules) [M.IsQuasicoherent]
variable (U : X.affineOpens)

def restrictedIso :
    (ModuleCat.extendScalars g.appTop.hom).obj
      ((ModuleCat.restrictScalars (U.1.ι ≫ π).appTop.hom).obj
        ((AffineSectionIs.Construction.AffineSectionAdjunction.sections U.1.toScheme).obj (M.restrict U.1.ι))) ≅
    (ModuleCat.restrictScalars ((f ⁻¹ᵁ U.1).ι ≫ ρ).appTop.hom).obj
      ((AffineSectionIs.Construction.AffineSectionAdjunction.sections (f ⁻¹ᵁ U.1).toScheme).obj
        ((Scheme.Modules.pullback (f ∣_ U.1)).obj (M.restrict U.1.ι))) := by
  have : IsAffine U.1.toScheme := U.2
  exact AffineSquare.Construction.AffineSquareSections.iso (f ∣_ U.1) (U.1.ι ≫ π) ((f ⁻¹ᵁ U.1).ι ≫ ρ) g
    ((isPullback_morphismRestrict f U.1).paste_vert h) (M.restrict U.1.ι)

theorem restricted_one (s : Γ(M.restrict U.1.ι, ⊤)) :
    (restrictedIso f π ρ g h M U).hom
      ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom]
        (show (ModuleCat.restrictScalars (U.1.ι ≫ π).appTop.hom).obj
          ((AffineSectionIs.Construction.AffineSectionAdjunction.sections U.1.toScheme).obj (M.restrict U.1.ι)) from s)) =
      PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map (f ∣_ U.1) (M.restrict U.1.ι) ⊤ s := by
  have : IsAffine U.1.toScheme := U.2
  dsimp only [restrictedIso]
  exact @AffineSquare.Construction.AffineSquareSections.one_tmul U.1.toScheme (f ⁻¹ᵁ U.1).toScheme S T
    ‹IsAffine U.1.toScheme› ‹IsAffine S› ‹IsAffine T›
    (f ∣_ U.1) (U.1.ι ≫ π) ((f ⁻¹ᵁ U.1).ι ≫ ρ) g
    ((isPullback_morphismRestrict f U.1).paste_vert h) (M.restrict U.1.ι) inferInstance s

omit [IsAffine S] [IsAffine T] [M.IsQuasicoherent] in
def targetIso :
    (ModuleCat.restrictScalars ((f ⁻¹ᵁ U.1).ι ≫ ρ).appTop.hom).obj
      ((AffineSectionIs.Construction.AffineSectionAdjunction.sections (f ⁻¹ᵁ U.1).toScheme).obj
        ((Scheme.Modules.pullback (f ∣_ U.1)).obj (M.restrict U.1.ι))) ≅
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op (f ⁻¹ᵁ U.1)) :=
  (ModuleCat.restrictScalars ((f ⁻¹ᵁ U.1).ι ≫ ρ).appTop.hom).mapIso
      ((AffineSectionIs.Construction.AffineSectionAdjunction.sections (f ⁻¹ᵁ U.1).toScheme).mapIso ((OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U.1).app M)) ≪≫
    BaseOpen.Construction.BaseOpenSections.iso ρ ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U.1)

omit [IsAffine S] [IsAffine T] [M.IsQuasicoherent] in
theorem target_apply (s : Γ((Scheme.Modules.pullback (f ∣_ U.1)).obj (M.restrict U.1.ι), ⊤)) :
    (targetIso f ρ M U).hom s =
      (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U.1)).hom
        (((OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U.1).hom.app M).app ⊤ s) := rfl

omit [IsAffine S] [IsAffine T] [M.IsQuasicoherent] in
theorem target_normalization (s : Γ(M, U.1)) :
    (targetIso f ρ M U).hom
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map (f ∣_ U.1) (M.restrict U.1.ι) ⊤
        ((SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U.1).inv s)) = PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U.1 s :=
  (target_apply f ρ M U _).trans (OpenPullbackId.Construction.OpenPullbackSections.normalization f M U.1 s)

omit [IsAffine S] [IsAffine T] [M.IsQuasicoherent] in
theorem target_base_normalization (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U.1)) :
    (targetIso f ρ M U).hom
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map (f ∣_ U.1) (M.restrict U.1.ι) ⊤
        ((BaseOpen.Construction.BaseOpenSections.iso π M U.1).inv s)) = PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U.1 s := by
  let t : Γ(M.restrict U.1.ι, ⊤) → Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U.1) :=
    fun z => (targetIso f ρ M U).hom
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map (f ∣_ U.1) (M.restrict U.1.ι) ⊤ z)
  have ha := congrArg t (BaseOpen.Construction.BaseOpenSections.inv_apply π M U.1 s)
  exact ha.trans (target_normalization f ρ M U s)

private def chainIso {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    {A B : ModuleCat.{u} R} {C D : ModuleCat.{u} S}
    (a : A ≅ B) (b : (ModuleCat.extendScalars g).obj B ≅ C) (c : C ≅ D) :
    (ModuleCat.extendScalars g).obj A ≅ D :=
  (ModuleCat.extendScalars g).mapIso a ≪≫ b ≪≫ c

private theorem chain_one {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    {A B : ModuleCat.{u} R} {C D : ModuleCat.{u} S}
    (a : A ≅ B) (b : (ModuleCat.extendScalars g).obj B ≅ C) (c : C ≅ D) (s : A) :
    (chainIso g a b c).hom ((1 : S) ⊗ₜ[R,g] s) =
      c.hom (b.hom ((1 : S) ⊗ₜ[R,g] (a.hom s))) := by
  simp only [chainIso, Iso.trans_hom, Functor.mapIso_hom, ModuleCat.comp_apply,
    ModuleCat.ExtendScalars.map_tmul]

private theorem chain_normalization {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    {A B : ModuleCat.{u} R} {C D : ModuleCat.{u} S}
    (a : A ≅ B) (b : (ModuleCat.extendScalars g).obj B ≅ C) (c : C ≅ D)
    (v : B → C) (w : A → D)
    (hb : ∀ z, b.hom ((1 : S) ⊗ₜ[R,g] z) = v z)
    (hc : ∀ z, c.hom (v (a.hom z)) = w z) (s : A) :
    (chainIso g a b c).hom ((1 : S) ⊗ₜ[R,g] s) = w s := by
  rw [chain_one, hb, hc]

private def chainData {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    {A B : ModuleCat.{u} R} {C D : ModuleCat.{u} S}
    (a : A ≅ B) (b : (ModuleCat.extendScalars g).obj B ≅ C) (c : C ≅ D)
    (v : B → C) (w : A → D)
    (hb : ∀ z, b.hom ((1 : S) ⊗ₜ[R,g] z) = v z)
    (hc : ∀ z, c.hom (v (a.hom z)) = w z) :
    {e : (ModuleCat.extendScalars g).obj A ≅ D // ∀ s, e.hom ((1 : S) ⊗ₜ[R,g] s) = w s} :=
  ⟨chainIso g a b c, chain_normalization g a b c v w hb hc⟩

def data :
    {e : (ModuleCat.extendScalars g.appTop.hom).obj ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U.1)) ≅
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op (f ⁻¹ᵁ U.1)) //
      ∀ s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U.1),
        e.hom ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s) =
          PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U.1 s} := by
  let A := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U.1)
  let B := (ModuleCat.restrictScalars (U.1.ι ≫ π).appTop.hom).obj
    ((AffineSectionIs.Construction.AffineSectionAdjunction.sections U.1.toScheme).obj (M.restrict U.1.ι))
  let C := (ModuleCat.restrictScalars ((f ⁻¹ᵁ U.1).ι ≫ ρ).appTop.hom).obj
    ((AffineSectionIs.Construction.AffineSectionAdjunction.sections (f ⁻¹ᵁ U.1).toScheme).obj
      ((Scheme.Modules.pullback (f ∣_ U.1)).obj (M.restrict U.1.ι)))
  let D := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op (f ⁻¹ᵁ U.1))
  let v : B → C := PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map (f ∣_ U.1) (M.restrict U.1.ι) ⊤
  let w : A → D := PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U.1
  have hb : ∀ z : B, (restrictedIso f π ρ g h M U).hom
      ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] z) = v z := by
    intro z
    exact @restricted_one X Y S T ‹IsAffine S› ‹IsAffine T› f π ρ g h M
      ‹M.IsQuasicoherent› U z
  have hn : ∀ z : A, (targetIso f ρ M U).hom (v ((BaseOpen.Construction.BaseOpenSections.iso π M U.1).inv z)) = w z := by
    intro z
    exact target_base_normalization f π ρ M U z
  exact @chainData Γ(S, ⊤) Γ(T, ⊤) inferInstance inferInstance g.appTop.hom
    A B C D (BaseOpen.Construction.BaseOpenSections.iso π M U.1).symm
    (restrictedIso f π ρ g h M U) (targetIso f ρ M U) v w hb hn

def iso :
    (ModuleCat.extendScalars g.appTop.hom).obj ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U.1)) ≅
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op (f ⁻¹ᵁ U.1)) :=
  (data f π ρ g h M U).val

theorem one_tmul (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U.1)) :
    (iso f π ρ g h M U).hom ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s) =
      PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U.1 s :=
  (data f π ρ g h M U).property s

end Construction.AffineOpenSquare

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineOpen
