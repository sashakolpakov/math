import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Topology.Sheaves.Stalks

/-! # Sheaf Local Bijectivity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SheafLocalBijectivity.BundleCycles

noncomputable section

/-! # LineBundleCycles: invertibility of actual sheaf maps can be checked on open neighborhoods -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} {F G : TopCat.Sheaf Ab.{0} X} (φ : F ⟶ G)

theorem sheafMap_injective_of_local (U : Opens X)
    (h : ∀ x ∈ U, ∃ V : Opens X, V ≤ U ∧ x ∈ V ∧ Function.Injective (φ.hom.app (op V))) :
    Function.Injective (φ.hom.app (op U)) := by
  intro s t heq
  apply TopCat.Presheaf.IsSheaf.section_ext (F := F.presheaf) F.property
  intro x hx
  obtain ⟨V, hVU, hxV, hinj⟩ := h x hx
  refine ⟨V, hVU, hxV, hinj ?_⟩
  have he := congrArg (G.presheaf.map (homOfLE hVU).op) heq
  exact (ConcreteCategory.congr_hom (φ.hom.naturality (homOfLE hVU).op) s).trans
    (he.trans (ConcreteCategory.congr_hom (φ.hom.naturality (homOfLE hVU).op) t).symm)

theorem sheafMap_surjective_of_local (U : Opens X)
    (hinj : ∀ V ≤ U, Function.Injective (φ.hom.app (op V)))
    (hsurj : ∀ (t : G.presheaf.obj (op U)) x, x ∈ U →
      ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        ∃ s : F.presheaf.obj (op V), φ.hom.app (op V) s = G.presheaf.map (homOfLE hVU).op t) :
    Function.Surjective (φ.hom.app (op U)) := by
  intro t
  choose V hVU hxV s hs using (fun x : U => hsurj t x.val x.property)
  have hcover : U ≤ iSup V := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf V s := by
    intro x y
    apply hinj (V x ⊓ V y) (inf_le_left.trans (hVU x))
    have hx := ConcreteCategory.congr_hom (φ.hom.naturality ((V x).infLELeft (V y)).op) (s x)
    have hy := ConcreteCategory.congr_hom (φ.hom.naturality ((V x).infLERight (V y)).op) (s y)
    refine hx.trans ((congrArg (G.presheaf.map ((V x).infLELeft (V y)).op) (hs x)).trans ?_)
    refine Eq.trans ?_ ((congrArg (G.presheaf.map ((V x).infLERight (V y)).op) (hs y)).symm.trans hy.symm)
    rw [← ConcreteCategory.comp_apply, ← G.presheaf.map_comp,
      ← ConcreteCategory.comp_apply, ← G.presheaf.map_comp]
    rfl
  obtain ⟨a, ha, _⟩ := F.existsUnique_gluing' V U (fun x => homOfLE (hVU x)) hcover s hcompat
  refine ⟨a, ?_⟩
  apply G.eq_of_locally_eq' V U (fun x => homOfLE (hVU x)) hcover
  intro x
  exact (ConcreteCategory.congr_hom (φ.hom.naturality (homOfLE (hVU x)).op) a).symm.trans
    ((congrArg (φ.hom.app (op (V x))) (ha x)).trans (hs x))

theorem sheafMap_bijective_of_local (U : Opens X)
    (h : ∀ x ∈ U, ∃ V : Opens X, V ≤ U ∧ x ∈ V ∧
      ∀ W ≤ V, Function.Bijective (φ.hom.app (op W))) :
    Function.Bijective (φ.hom.app (op U)) := by
  have hinj : ∀ W ≤ U, Function.Injective (φ.hom.app (op W)) := by
    intro W hWU
    apply sheafMap_injective_of_local φ W
    intro x hx
    obtain ⟨V, _, hxV, hV⟩ := h x (hWU hx)
    exact ⟨W ⊓ V, inf_le_left, ⟨hx, hxV⟩, (hV (W ⊓ V) inf_le_right).1⟩
  refine ⟨hinj U le_rfl, sheafMap_surjective_of_local φ U hinj ?_⟩
  intro t x hx
  obtain ⟨V, hVU, hxV, hV⟩ := h x hx
  exact ⟨V, hVU, hxV, (hV V le_rfl).2 (G.presheaf.map (homOfLE hVU).op t)⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SheafLocalBijectivity.BundleCycles
