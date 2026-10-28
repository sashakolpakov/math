import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapBasisExtension

/-! # Basis Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module

noncomputable section

/-! Module maps are determined on a basis, and compatible isomorphisms on a basis extend to an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {X : Scheme.{u}} {ι : Type v} (B : ι → X.Opens)
variable (hB : Opens.IsBasis (Set.range B)) {M N : X.Modules}

include hB in
theorem BasisIsomorphisms.moduleMap_eq_of_basis (f g : M ⟶ N)
    (h : ∀ i, f.app (B i) = g.app (B i)) : f = g := by
  apply (Scheme.Modules.toPresheaf X).map_injective
  exact TopCat.Sheaf.hom_ext M.presheaf ⟨N.presheaf, N.isSheaf⟩ hB h

theorem MapBasisExtension.ModuleBasisMap.extend_unique (D : MapBasisExtension.ModuleBasisMap B M N) (f : M ⟶ N)
    (hf : ∀ i (s : Γ(M, B i)), f.app (B i) s = D.app i s) : f = D.extend hB := by
  apply BasisIsomorphisms.moduleMap_eq_of_basis B hB
  intro i
  apply ConcreteCategory.hom_ext
  intro s
  exact (hf i s).trans (D.extend_app hB i s).symm

theorem MapBasisExtension.ModuleBasisMap.extend_isIso (D : MapBasisExtension.ModuleBasisMap B M N)
    (hD : ∀ i, Function.Bijective (D.app i)) : IsIso (D.extend hB) := by
  let f : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) :=
    ⟨(D.extend hB).mapPresheaf⟩
  have hf : IsIso f := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hB
    intro i
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hi : (fun s : Γ(M, B i) => f.hom.app (.op (B i)) s) = D.app i := by
      funext s
      exact D.extend_app hB i s
    change Function.Bijective (fun s : Γ(M, B i) => f.hom.app (.op (B i)) s)
    rw [hi]
    exact hD i
  have : IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map f) :=
    @Functor.map_isIso _ _ _ _ _ _ (TopCat.Sheaf.forget AddCommGrpCat.{u} X) f hf
  have : IsIso ((Scheme.Modules.toPresheaf X).map (D.extend hB)) :=
    inferInstanceAs (IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map f))
  exact isIso_of_reflects_iso (D.extend hB) (Scheme.Modules.toPresheaf X)

def MapBasisExtension.ModuleBasisMap.extendIso (D : MapBasisExtension.ModuleBasisMap B M N)
    (hD : ∀ i, Function.Bijective (D.app i)) : M ≅ N :=
  @asIso X.Modules _ M N (D.extend hB) (D.extend_isIso B hB hD)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module
