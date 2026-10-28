import OAI.AlgebraicGeometry.Divisors.LineBundles.Module.BasisPresheafHom
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ModuleBasisIso

/-! # Module Hom Of Basis -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ModuleHomOfBasis.BundleCycles

noncomputable section

/-! Basiswise linear maps glue to genuine scheme-module maps;
basiswise isomorphisms give actual module-sheaf isomorphisms. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : Scheme.{0}} (M N : X.Modules) (B : Set X.Opens) (hB : Opens.IsBasis B)
    (φ : ∀ U : B, Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(N, U.1))
    (hφ : ∀ (U V : B) (h : U.1 ≤ V.1) (m : Γ(M, V.1)),
      φ U (M.presheaf.map (homOfLE h).op m) = N.presheaf.map (homOfLE h).op (φ V m))

theorem moduleBasisPresheafHom_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
    (Module.BasisPresheafHom.BundleCycles.moduleBasisPresheafHom M N B hB φ hφ).app (op U) (r • m) =
      r • (Module.BasisPresheafHom.BundleCycles.moduleBasisPresheafHom M N B hB φ hφ).app (op U) m := by
  let ψ := Module.BasisPresheafHom.BundleCycles.moduleBasisPresheafHom M N B hB φ hφ
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  refine ⟨V, hVU, hxV, ?_⟩
  have hn (s : Γ(M, U)) := ConcreteCategory.congr_hom (ψ.naturality (homOfLE hVU).op) s
  have ha (s : Γ(M, V)) := Module.BasisPresheafHom.BundleCycles.moduleBasisPresheafHom_app M N B hB φ hφ ⟨V, hV⟩ s
  calc
    N.presheaf.map (homOfLE hVU).op (ψ.app (op U) (r • m)) =
        ψ.app (op V) (M.presheaf.map (homOfLE hVU).op (r • m)) := (hn _).symm
    _ = φ ⟨V, hV⟩ (M.presheaf.map (homOfLE hVU).op (r • m)) := ha _
    _ = X.presheaf.map (homOfLE hVU).op r • φ ⟨V, hV⟩ (M.presheaf.map (homOfLE hVU).op m) := by
      rw [Scheme.Modules.map_smul, map_smul]
    _ = X.presheaf.map (homOfLE hVU).op r • N.presheaf.map (homOfLE hVU).op (ψ.app (op U) m) :=
      congrArg (fun s => X.presheaf.map (homOfLE hVU).op r • s) ((ha _).symm.trans (hn m))
    _ = N.presheaf.map (homOfLE hVU).op (r • ψ.app (op U) m) :=
      (Scheme.Modules.map_smul N (homOfLE hVU) r (ψ.app (op U) m)).symm

def schemeModuleHomOfBasis : M ⟶ N :=
  ⟨PresheafOfModules.homMk (Module.BasisPresheafHom.BundleCycles.moduleBasisPresheafHom M N B hB φ hφ)
    (fun U r m => moduleBasisPresheafHom_smul M N B hB φ hφ U.unop r m)⟩

theorem schemeModuleHomOfBasis_app (U : B) (m : Γ(M, U.1)) :
    (schemeModuleHomOfBasis M N B hB φ hφ).app U.1 m = φ U m :=
  Module.BasisPresheafHom.BundleCycles.moduleBasisPresheafHom_app M N B hB φ hφ U m

theorem schemeModuleHomOfBasis_isIso (hbij : ∀ U, Function.Bijective (φ U)) :
    IsIso (schemeModuleHomOfBasis M N B hB φ hφ) := by
  apply ModuleBasisIso.BundleCycles.schemeModule_isIso_of_basis _ hB
  intro U hU
  have he : ((schemeModuleHomOfBasis M N B hB φ hφ).app U : Γ(M, U) → Γ(N, U)) = φ ⟨U, hU⟩ :=
    funext (schemeModuleHomOfBasis_app M N B hB φ hφ ⟨U, hU⟩)
  rw [he]
  exact hbij ⟨U, hU⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ModuleHomOfBasis.BundleCycles
