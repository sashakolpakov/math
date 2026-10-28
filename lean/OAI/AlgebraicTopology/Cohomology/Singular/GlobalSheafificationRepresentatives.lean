import OAI.AlgebraicTopology.Cohomology.Singular.SheafQuasiIso
import OAI.AlgebraicTopology.Cohomology.Singular.FiniteGermGluing
import OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf
import OAI.AlgebraicTopology.DeRham.Comparison.CompactShrinkingCover
import Mathlib.Topology.Sheaves.LocallySurjective

/-! # Global Sheafification Representatives -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.GlobalSheafificationRepresentatives

noncomputable section

/-!
# Genuine representatives of sheafified singular cochains

The sheafification unit has local representatives and preserves the actual
stalks. On compact Hausdorff spaces a finite shrinking allows these local
singular cochains to be represented by one global singular cochain. The
finite gluing step uses the actual functions on continuous simplices.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open _root_.TopCat.Presheaf

variable {R : Type} [Ring R] {X : TopCat.{0}}

attribute [local instance] StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

/-- A global section of a genuine sheafification has actual presheaf
representatives on an open cover indexed by the points. -/
theorem sheafification_global_local_representatives
    (F : X.Presheaf (ModuleCat.{0} R))
    (s : (CategoryTheory.sheafify (Opens.grothendieckTopology X) F).obj (op ⊤)) :
    ∃ (U : X → Opens X) (_hx : ∀ x : X, x ∈ U x)
      (c : ∀ x : X, F.obj (op (U x))),
      ∀ x : X,
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F).app (op (U x))
          (c x) =
        (CategoryTheory.sheafify (Opens.grothendieckTopology X) F).map
          (homOfLE (show U x ≤ ⊤ from le_top)).op s := by
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) F
  have hlocal : TopCat.Presheaf.IsLocallySurjective η := by
    apply (locally_surjective_iff_surjective_on_stalks η).2
    intro x
    let := stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} R) F
    exact (ConcreteCategory.bijective_of_isIso
      ((stalkFunctor (ModuleCat.{0} R) x).map η)).2
  have hpoint : ∀ x : X, ∃ (U : Opens X), x ∈ U ∧
      ∃ c : F.obj (op U), η.app (op U) c =
        (CategoryTheory.sheafify (Opens.grothendieckTopology X) F).map
          (homOfLE (show U ≤ ⊤ from le_top)).op s := by
    intro x
    obtain ⟨U, hU, ⟨c, hc⟩, hx⟩ :=
      (isLocallySurjective_iff η).mp hlocal ⊤ s x (by simp)
    exact ⟨U, hx, c, hc⟩
  choose U hx c hc using hpoint
  exact ⟨U, hx, c, hc⟩

/-- Two local representatives of the same global sheafified section have
equal genuine presheaf germs wherever both are defined. -/
theorem sheafification_local_representatives_germ_eq
    (F : X.Presheaf (ModuleCat.{0} R))
    (s : (CategoryTheory.sheafify (Opens.grothendieckTopology X) F).obj (op ⊤))
    (U V : Opens X) (a : F.obj (op U)) (b : F.obj (op V))
    (ha : (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F).app (op U) a =
      (CategoryTheory.sheafify (Opens.grothendieckTopology X) F).map
        (homOfLE (show U ≤ ⊤ from le_top)).op s)
    (hb : (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F).app (op V) b =
      (CategoryTheory.sheafify (Opens.grothendieckTopology X) F).map
        (homOfLE (show V ≤ ⊤ from le_top)).op s)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    F.germ U x hxU a = F.germ V x hxV b := by
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) F
  let := stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} R) F
  apply (ConcreteCategory.bijective_of_isIso
    ((stalkFunctor (ModuleCat.{0} R) x).map η)).1
  rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ
      (CategoryTheory.sheafify (Opens.grothendieckTopology X) F) U x hxU
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) F).app (op U) a) =
    TopCat.Presheaf.germ
      (CategoryTheory.sheafify (Opens.grothendieckTopology X) F) V x hxV
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) F).app (op V) b)
  rw [ha, hb, germ_res_apply, germ_res_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every global section of the sheafification of genuine singular cochains
on a compact Hausdorff space has a genuine global singular cochain
representative. This is proved by a finite shrinking and actual cochain
gluing; no general assertion about flabby presheaves is used. -/
theorem singularCochain_sheafification_top_surjective
    (A : ModuleCat.{0} R) (X : TopCat.{0}) [CompactSpace X] [T2Space X] (n : ℕ) :
    Function.Surjective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A X n)).app (op ⊤)) := by
  intro s
  let F : X.Presheaf (ModuleCat.{0} R) := DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A X n
  let G : X.Presheaf (ModuleCat.{0} R) :=
    CategoryTheory.sheafify (Opens.grothendieckTopology X) F
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) F
  obtain ⟨U, hxU, c, hc⟩ := sheafification_global_local_representatives F s
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  obtain ⟨k, r, V, hV, hVU⟩ := DeRham.Comparison.CompactShrinkingCover.exists_finite_shrinking_cover U hU
  have hcompat : ∀ i j (x : X) (hxi : x ∈ U (r i)) (hxj : x ∈ U (r j)),
      F.germ (U (r i)) x hxi (c (r i)) = F.germ (U (r j)) x hxj (c (r j)) := by
    intro i j x hxi hxj
    exact sheafification_local_representatives_germ_eq F s
      (U (r i)) (U (r j)) (c (r i)) (c (r j)) (hc (r i)) (hc (r j)) x hxi hxj
  obtain ⟨g, hg⟩ := FiniteGermGluing.exists_global_singularCochain_of_finite_germ_compatible
    A X n (fun i : Fin k => U (r i)) V hV hVU (fun i => c (r i)) hcompat
  refine ⟨g, ?_⟩
  apply TopCat.Presheaf.section_ext
    ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).obj F) ⊤
  intro x hx
  have hxV : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxV
  have hxiU : x ∈ U (r i) := hVU i (subset_closure hxi)
  have hmap := congrArg ((stalkFunctor (ModuleCat.{0} R) x).map η) (hg i x hxiU)
  calc
    G.germ ⊤ x hx (η.app (op ⊤) g) =
        G.germ (U (r i)) x hxiU (η.app (op (U (r i))) (c (r i))) := by
      exact (stalkFunctor_map_germ_apply ⊤ x hx η g).symm.trans
        (hmap.trans (stalkFunctor_map_germ_apply (U (r i)) x hxiU η (c (r i))))
    _ = G.germ ⊤ x hx s := by
      change G.germ (U (r i)) x hxiU
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) F).app
          (op (U (r i))) (c (r i))) = _
      rw [hc (r i)]
      exact G.germ_res_apply (homOfLE (show U (r i) ≤ ⊤ from le_top)) x hxiU s

/-- Categorical form of the genuine global representative theorem. -/
theorem epi_singularCochain_sheafification_top
    (A : ModuleCat.{0} R) (X : TopCat.{0}) [CompactSpace X] [T2Space X] (n : ℕ) :
    Epi ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A X n)).app (op ⊤)) :=
  (ModuleCat.epi_iff_surjective _).2
    (singularCochain_sheafification_top_surjective A X n)

end

end OAI.AlgebraicTopology.Cohomology.Singular.GlobalSheafificationRepresentatives
