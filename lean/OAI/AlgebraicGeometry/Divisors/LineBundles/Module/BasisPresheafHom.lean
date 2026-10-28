import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Basis Presheaf Hom -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Module.BasisPresheafHom.BundleCycles

noncomputable section

/-! Compatible linear maps on a basis extend to the actual
underlying abelian sheaves of scheme modules. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : Scheme.{0}} (M N : X.Modules) (B : Set X.Opens) (hB : Opens.IsBasis B)
    (φ : ∀ U : B, Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(N, U.1))
    (hφ : ∀ (U V : B) (h : U.1 ≤ V.1) (m : Γ(M, V.1)),
      φ U (M.presheaf.map (homOfLE h).op m) = N.presheaf.map (homOfLE h).op (φ V m))

include hB in
theorem moduleBasis_range_basis : Opens.IsBasis (Set.range (fun U : B => U.1)) := by
  have he : Set.range (fun U : B => U.1) = B := by
    ext U
    exact ⟨fun ⟨V, hV⟩ => hV ▸ V.property, fun hU => ⟨⟨U, hU⟩, rfl⟩⟩
  exact he.symm ▸ hB

def moduleBasisRestrictedHom :
    (inducedFunctor (fun U : B => U.1)).op ⋙ M.presheaf ⟶
      (inducedFunctor (fun U : B => U.1)).op ⋙ N.presheaf where
  app U := AddCommGrpCat.ofHom (φ U.unop).toAddMonoidHom
  naturality {U V} f := by
    ext m
    exact hφ V.unop U.unop (leOfHom f.unop.hom) m

def moduleBasisPresheafHom : M.presheaf ⟶ N.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom M.presheaf ⟨N.presheaf, N.isSheaf⟩
    (moduleBasis_range_basis B hB) (moduleBasisRestrictedHom M N B φ hφ)

theorem moduleBasisPresheafHom_app (U : B) (m : Γ(M, U.1)) :
    (moduleBasisPresheafHom M N B hB φ hφ).app (op U.1) m = φ U m :=
  ConcreteCategory.congr_hom (TopCat.Sheaf.extend_hom_app M.presheaf ⟨N.presheaf, N.isSheaf⟩
    (moduleBasis_range_basis B hB) (moduleBasisRestrictedHom M N B φ hφ) U) m

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Module.BasisPresheafHom.BundleCycles
