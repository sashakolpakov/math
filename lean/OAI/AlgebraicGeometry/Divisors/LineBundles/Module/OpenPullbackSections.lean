import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenRestriction

/-! # Open Pullback Sections -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Divisors.LineBundles

/-! # LineBundleCycles: actual section pullback from the module-sheaf adjunction -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)

def Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen (U : Y.Opens) :
    Γ(M, U) ⟶ Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U

theorem Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_smul (U : Y.Opens) (r : Γ(Y, U)) (s : Γ(M, U)) :
    Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M U (r • s) =
      f.app U r • Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M U s :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app_smul r s

theorem Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_restrict {U V : Y.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map
        (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op
        (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M U s) =
      Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M V (M.presheaf.map (homOfLE h).op s) :=
  (ConcreteCategory.congr_hom
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality (homOfLE h).op) s).symm

theorem Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen_naturality {M N : Y.Modules} (φ : M ⟶ N)
    (U : Y.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ U) (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M U s) =
      Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f N U (φ.app U s) := by
  have h := congrArg (fun k : M ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj N) =>
    k.app U s) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ)
  exact h.symm

def Module.OpenPullbackSections.BundleCycles.moduleGlobalSectionPullback (s : Γ(M, ⊤)) : Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
  ((Scheme.Modules.pullback f).obj M).presheaf.map
    (homOfLE (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) from fun _ _ => trivial)).op
      (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen f M ⊤ s)

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.pullbackSection (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y) (s : Γ(L.sheaf, ⊤)) :
    Γ((L.pullback f).sheaf, ⊤) := Module.OpenPullbackSections.BundleCycles.moduleGlobalSectionPullback f L.sheaf s

end AlgebraicGeometry.Divisors.LineBundles

namespace AlgebraicGeometry.Divisors.LineBundles.Module.OpenPullbackSections.BundleCycles

/-! # LineBundleCycles: actual section compatibility of open restriction with module-sheaf pullback -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (M : Y.Modules)

theorem moduleOpenPullbackIso_section (U : Y.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.restrictFunctorIsoPullback i).app M).hom.app (i ⁻¹ᵁ U)
      (M.presheaf.map (homOfLE (i.image_preimage_le U)).op s) =
      moduleSectionPullbackOnOpen i M U s := by
  have H := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction i)
    (Scheme.Modules.pullbackPushforwardAdjunction i) M
  exact congrArg (fun k => k.app U s) H

theorem moduleOpenPullbackIso_inv_section (U : Y.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.restrictFunctorIsoPullback i).app M).inv.app (i ⁻¹ᵁ U)
      (moduleSectionPullbackOnOpen i M U s) =
      M.presheaf.map (homOfLE (i.image_preimage_le U)).op s := by
  rw [← moduleOpenPullbackIso_section]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k => k.app (i ⁻¹ᵁ U)) ((Scheme.Modules.restrictFunctorIsoPullback i).app M).hom_inv_id) _

end AlgebraicGeometry.Divisors.LineBundles.Module.OpenPullbackSections.BundleCycles

end

end OAI
