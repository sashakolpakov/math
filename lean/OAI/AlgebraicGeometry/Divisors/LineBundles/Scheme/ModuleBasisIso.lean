import OAI.AlgebraicGeometry.Divisors.LineBundles.SheafBasisBijectivity
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Module Basis Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ModuleBasisIso.BundleCycles

noncomputable section

/-! An actual module-sheaf map is an isomorphism if its section maps
are bijective on a basis of scheme opens. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    {B : Set X.Opens} (hB : Opens.IsBasis B)
    (hφ : ∀ U ∈ B, Function.Bijective (φ.app U))

include hB hφ in
theorem schemeModule_isIso_of_basis : IsIso φ := by
  let F : TopCat.Sheaf Ab.{0} X := ⟨M.presheaf, M.isSheaf⟩
  let G : TopCat.Sheaf Ab.{0} X := ⟨N.presheaf, N.isSheaf⟩
  let ψ : F ⟶ G := ⟨φ.mapPresheaf⟩
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact SheafBasisBijectivity.BundleCycles.sheafMap_bijective_of_basis ψ hB hφ U

theorem schemeModule_isIso_of_affineSections (h : ∀ U : X.affineOpens, Function.Bijective (φ.app U.1)) :
    IsIso φ :=
  schemeModule_isIso_of_basis φ X.isBasis_affineOpens (fun U hU => h ⟨U, hU⟩)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ModuleBasisIso.BundleCycles
