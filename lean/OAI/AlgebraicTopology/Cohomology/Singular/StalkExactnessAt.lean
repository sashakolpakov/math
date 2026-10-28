import OAI.AlgebraicTopology.Cohomology.Singular.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Sheaves.Abelian

/-! # Stalk Exactness At -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt

noncomputable section

/-!
# Local primitives imply exactness of actual stalk complexes

The stalks here are mathlib's colimits over open neighborhoods. A closed germ
first has a representative whose differential becomes zero on a smaller
neighborhood. An actual local primitive of that representative then supplies
a primitive germ. The local primitive premise is explicit and is not asserted
for any particular geometric complex by this file.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

universe u

variable {R : Type} [Ring R] {X : TopCat.{u}}

/-- Module filtered colimits have the usual underlying filtered colimit of groups,
including when the carrier universe is larger than the scalar universe. -/
local instance stalkModulesForget₂PreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (ModuleCat.{u,0} R) AddCommGrpCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone
          (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ (ModuleCat.{u,0} R) AddCommGrpCat.{u})) }

/-- The underlying-set functor preserves the filtered colimits defining stalks. -/
local instance stalkModulesForgetPreservesFilteredColimits :
    PreservesFilteredColimits (forget (ModuleCat.{u,0} R)) :=
  Limits.comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{u,0} R) AddCommGrpCat.{u}) (forget AddCommGrpCat.{u})

/-- A section has zero germ exactly when it vanishes on a smaller neighborhood. -/
theorem germ_eq_zero_iff_locally_zero (F : X.Presheaf (ModuleCat.{u,0} R))
    (x : X) (U : Opens X) (hxU : x ∈ U) (s : F.obj (op U)) :
    F.germ U x hxU s = 0 ↔
      ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U), F.map i.op s = 0 := by
  constructor
  · intro hs
    have hzero : F.germ U x hxU s = F.germ U x hxU 0 := by
      simpa only [map_zero] using hs
    obtain ⟨V, hxV, i, j, hij⟩ := F.germ_eq x hxU hxU s 0 hzero
    exact ⟨V, hxV, i, by simpa only [map_zero] using hij⟩
  · rintro ⟨V, hxV, i, hs⟩
    rw [← F.germ_res_apply i x hxV s, hs, map_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An explicit local primitive condition for a short complex of module
presheaves implies exactness after taking the actual stalk at `x`. -/
theorem stalk_exact_of_locally_exact
    (S : ShortComplex (X.Presheaf (ModuleCat.{u,0} R))) (x : X)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U) (s : S.X₂.obj (op U)),
      S.g.app (op U) s = 0 →
        ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U) (t : S.X₁.obj (op V)),
          S.f.app (op V) t = S.X₂.map i.op s) :
    (S.map (stalkFunctor (ModuleCat.{u,0} R) x)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  change (stalkFunctor (ModuleCat.{u,0} R) x).map S.g z = 0 at hz
  obtain ⟨U, hxU, s, rfl⟩ := S.X₂.exists_germ_eq z
  rw [stalkFunctor_map_germ_apply] at hz
  obtain ⟨V, hxV, i, hi⟩ :=
    (germ_eq_zero_iff_locally_zero S.X₃ x U hxU (S.g.app (op U) s)).mp hz
  have hclosed : S.g.app (op V) (S.X₂.map i.op s) = 0 := by
    have hnat := ConcreteCategory.congr_hom (S.g.naturality i.op) s
    exact hnat.trans hi
  obtain ⟨W, hxW, j, t, ht⟩ := hlocal V hxV (S.X₂.map i.op s) hclosed
  refine ⟨S.X₁.germ W x hxW t, ?_⟩
  change (stalkFunctor (ModuleCat.{u,0} R) x).map S.f (S.X₁.germ W x hxW t) =
    S.X₂.germ U x hxU s
  calc
    _ = S.X₂.germ W x hxW (S.f.app (op W) t) :=
      stalkFunctor_map_germ_apply W x hxW S.f t
    _ = S.X₂.germ W x hxW (S.X₂.map j.op (S.X₂.map i.op s)) :=
      congrArg (S.X₂.germ W x hxW) ht
    _ = S.X₂.germ V x (j.le hxW) (S.X₂.map i.op s) :=
      S.X₂.germ_res_apply j x hxW _
    _ = S.X₂.germ U x hxU s := S.X₂.germ_res_apply i x (j.le hxW) s

/-- A cochain complex of module presheaves has exact stalks in degree `n+1`
whenever each closed degree-`n+1` section has an actual local degree-`n` primitive. -/
theorem stalkComplex_exactAt_succ_of_local_primitives
    (K : CochainComplex (X.Presheaf (ModuleCat.{u,0} R)) ℕ) (x : X) (n : ℕ)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U) (s : (K.X (n + 1)).obj (op U)),
      (K.d (n + 1) (n + 2)).app (op U) s = 0 →
        ∃ (V : Opens X) (_hxV : x ∈ V) (i : V ⟶ U) (t : (K.X n).obj (op V)),
          (K.d n (n + 1)).app (op V) t = (K.X (n + 1)).map i.op s) :
    (((stalkFunctor (ModuleCat.{u,0} R) x).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      K).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
    ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl))
    ((ComplexShape.up ℕ).next_eq'
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl))).2
  exact stalk_exact_of_locally_exact (K.sc' n (n + 1) (n + 2)) x hlocal

end

end OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt
