import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.OpenSectionPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackSquareSections

/-! # Pullback Open Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackOpenIso.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: a genuine open section pulled back through its open-scheme presentation -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (M : Y.Modules) (U : Y.Opens) (q : X ⟶ U.toScheme)

theorem modulePullbackOpenGlobalSection_hom (s : Γ(M, U)) :
    ((Scheme.Modules.pullback q).map ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).hom).app ⊤
      (OpenPullbackSections.BundleCycles.moduleGlobalSectionPullback q (M.restrict U.ι) (SectionHom.BundleCycles.moduleSectionAsGlobal M U s)) =
      SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen q ((Scheme.Modules.pullback U.ι).obj M) (U.ι ⁻¹ᵁ U) ⊤
        (fun x _ => (q x).property) (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen U.ι M U s) := by
  let htop : (⊤ : X.Opens) ≤ q ⁻¹ᵁ (⊤ : U.toScheme.Opens) := fun _ _ => trivial
  have H := SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen_naturality q
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).hom ⊤ ⊤ htop (SectionHom.BundleCycles.moduleSectionAsGlobal M U s)
  have H' := congrArg (SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen q ((Scheme.Modules.pullback U.ι).obj M) ⊤ ⊤ htop)
    (OpenSectionPullback.BundleCycles.moduleOpenPullbackIso_openGlobal M U s)
  have H'' := PullbackSquareSections.BundleCycles.moduleSectionPullbackToOpen_restrict_source q ((Scheme.Modules.pullback U.ι).obj M)
    (show (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U from fun x _ => x.property) ⊤
    htop (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen U.ι M U s)
  exact H.trans (H'.trans H'')

end

/-! # LineBundleCycles: the actual open base-change isomorphism for module pullback and its section formula -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)

def modulePullbackOpenIso :
    ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (M.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app ((Scheme.Modules.pullback f).obj M) ≪≫
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm

theorem modulePullbackOpenIso_section (s : Γ(M, U)) :
    (modulePullbackOpenIso f M U).hom.app ⊤
      (SectionHom.BundleCycles.moduleSectionAsGlobal ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)
        (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M U s)) =
      OpenPullbackSections.BundleCycles.moduleGlobalSectionPullback (f ∣_ U) (M.restrict U.ι) (SectionHom.BundleCycles.moduleSectionAsGlobal M U s) := by
  let V := f ⁻¹ᵁ U
  let q := f ∣_ U
  let e₁ := (Scheme.Modules.restrictFunctorIsoPullback V.ι).app ((Scheme.Modules.pullback f).obj M)
  let e₂ := (Scheme.Modules.pullbackComp V.ι f).app M
  let e₃ := (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M
  let e₄ := ((Scheme.Modules.pullbackComp q U.ι).app M).symm
  let e := (Scheme.Modules.pullback q).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M)
  let h₁ : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun x _ => x.property
  let h₂ : (⊤ : V.toScheme.Opens) ≤ (V.ι ≫ f) ⁻¹ᵁ U := fun x _ => x.property
  let h₃ : (⊤ : V.toScheme.Opens) ≤ (q ≫ U.ι) ⁻¹ᵁ U := fun x _ => (q x).property
  let s₀ := SectionHom.BundleCycles.moduleSectionAsGlobal ((Scheme.Modules.pullback f).obj M) V (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M U s)
  let s₁ := SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen V.ι ((Scheme.Modules.pullback f).obj M) V ⊤ h₁
    (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M U s)
  let s₂ := SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen (V.ι ≫ f) M U ⊤ h₂ s
  let s₃ := SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen (q ≫ U.ι) M U ⊤ h₃ s
  let s₄ := SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen q ((Scheme.Modules.pullback U.ι).obj M) (U.ι ⁻¹ᵁ U) ⊤ h₃
    (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen U.ι M U s)
  let s₅ := OpenPullbackSections.BundleCycles.moduleGlobalSectionPullback q (M.restrict U.ι) (SectionHom.BundleCycles.moduleSectionAsGlobal M U s)
  have H₁ : e₁.hom.app ⊤ s₀ = s₁ :=
    OpenSectionPullback.BundleCycles.moduleOpenPullbackIso_openGlobal ((Scheme.Modules.pullback f).obj M) V (OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M U s)
  have H₂ : e₂.hom.app ⊤ s₁ = s₂ := SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen_comp_hom V.ι f M U ⊤ h₂ s
  have H₃ : e₃.hom.app ⊤ s₂ = s₃ :=
    PullbackSquareSections.BundleCycles.moduleSectionPullbackToOpen_congr M (morphismRestrict_ι f U).symm U ⊤ h₂ h₃ s
  have H₄ : e₄.hom.app ⊤ s₃ = s₄ := SectionPullbackComposition.BundleCycles.moduleSectionPullbackToOpen_comp_inv q U.ι M U ⊤ h₃ s
  have H₅ : e.hom.app ⊤ s₅ = s₄ := modulePullbackOpenGlobalSection_hom M U q s
  have H₂₁ := (congrArg (fun z => e₂.hom.app ⊤ z) H₁).trans H₂
  have H₃₂₁ := (congrArg (fun z => e₃.hom.app ⊤ z) H₂₁).trans H₃
  have H₄₃₂₁ := (congrArg (fun z => e₄.hom.app ⊤ z) H₃₂₁).trans H₄
  have H := congrArg (fun z => e.inv.app ⊤ z) (H₄₃₂₁.trans H₅.symm)
  exact H.trans (ConcreteCategory.congr_hom (congrArg (fun k => k.app ⊤) e.hom_inv_id) s₅)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Module.PullbackOpenIso.BundleCycles
