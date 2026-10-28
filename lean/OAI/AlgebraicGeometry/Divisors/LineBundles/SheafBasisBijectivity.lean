import OAI.AlgebraicGeometry.Divisors.LineBundles.SheafLocalBijectivity
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Sheaf Basis Bijectivity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SheafBasisBijectivity.BundleCycles

noncomputable section

/-! Bijectivity of a genuine sheaf map on a basis implies bijectivity
on every open, using its actual stalk maps. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} {F G : TopCat.Sheaf Ab.{0} X} (φ : F ⟶ G)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hφ : ∀ U ∈ B, Function.Bijective (φ.hom.app (op U)))

include hB hφ in
theorem sheafMap_bijective_of_basis (U : Opens X) : Function.Bijective (φ.hom.app (op U)) := by
  have hstalk : ∀ x : X, Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab.{0} x).map φ.hom) := by
    intro x
    refine ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB (fun V hV => (hφ V hV).1) x, ?_⟩
    intro t
    obtain ⟨V, hxV, hV, t, rfl⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB G.presheaf x t
    obtain ⟨s, hs⟩ := (hφ V hV).2 t
    refine ⟨F.presheaf.germ V x hxV s, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hs]
  exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective φ U (fun x _ => hstalk x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SheafBasisBijectivity.BundleCycles
