import OAI.AlgebraicTopology.Cohomology.Singular.LocallyFiniteGermGluing
import OAI.AlgebraicTopology.Cohomology.Singular.GlobalSheafificationRepresentatives
import OAI.AlgebraicTopology.DeRham.Comparison.ParacompactShrinkingCover

/-! # Paracompact Sheafification Representatives -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ParacompactSheafificationRepresentatives

noncomputable section

/-!
# Genuine sheafified singular-cochain representatives on paracompact spaces

A locally finite open shrinking allows actual singular cochain germs to be
glued into one global cochain. Applied to the local representatives of a
sheafified section, this proves surjectivity of the actual sheafification
unit on global sections for paracompact Hausdorff spaces.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

variable {R : Type} [Ring R]

attribute [local instance] StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every global section of sheafified genuine singular cochains on a
paracompact Hausdorff space has an actual global singular cochain representative. -/
theorem singularCochain_sheafification_top_surjective_of_paracompact
    (A : ModuleCat.{0} R) (X : TopCat.{0}) [ParacompactSpace X] [T2Space X] (n : ℕ) :
    Function.Surjective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A X n)).app (op ⊤)) := by
  intro s
  let F : X.Presheaf (ModuleCat.{0} R) := DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A X n
  let G : X.Presheaf (ModuleCat.{0} R) :=
    CategoryTheory.sheafify (Opens.grothendieckTopology X) F
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) F
  obtain ⟨U, hxU, c, hc⟩ := GlobalSheafificationRepresentatives.sheafification_global_local_representatives F s
  have hU : iSup U = ⊤ := by
    apply le_antisymm le_top
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  obtain ⟨V, hV, hfinite, hVU⟩ := DeRham.Comparison.ParacompactShrinkingCover.exists_locallyFinite_shrinking_cover U hU
  have hcompat : ∀ i j (x : X) (hxi : x ∈ U i) (hxj : x ∈ U j),
      F.germ (U i) x hxi (c i) = F.germ (U j) x hxj (c j) := by
    intro i j x hxi hxj
    exact GlobalSheafificationRepresentatives.sheafification_local_representatives_germ_eq F s
      (U i) (U j) (c i) (c j) (hc i) (hc j) x hxi hxj
  obtain ⟨g, hg⟩ := LocallyFiniteGermGluing.exists_global_singularCochain_of_locallyFinite_germ_compatible
    A X n U V hV hfinite hVU c hcompat
  refine ⟨g, ?_⟩
  apply TopCat.Presheaf.section_ext
    ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)).obj F) ⊤
  intro x hx
  have hmap :
      ((stalkFunctor (ModuleCat.{0} R) x).map η)
          (F.germ ⊤ x (by trivial) g) =
        ((stalkFunctor (ModuleCat.{0} R) x).map η)
          (F.germ (U x) x (hxU x) (c x)) :=
    congrArg ((stalkFunctor (ModuleCat.{0} R) x).map η) (hg x x (hxU x))
  calc
    G.germ ⊤ x hx (η.app (op ⊤) g) =
        G.germ (U x) x (hxU x) (η.app (op (U x)) (c x)) := by
      simpa only [stalkFunctor_map_germ_apply] using hmap
    _ = G.germ ⊤ x hx s := by
      change G.germ (U x) x (hxU x)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) F).app
          (op (U x)) (c x)) = _
      rw [hc x]
      exact G.germ_res_apply (homOfLE (show U x ≤ ⊤ from le_top)) x (hxU x) s

/-- Categorical form of the actual representative theorem for paracompact
Hausdorff spaces. -/
theorem epi_singularCochain_sheafification_top_of_paracompact
    (A : ModuleCat.{0} R) (X : TopCat.{0}) [ParacompactSpace X] [T2Space X] (n : ℕ) :
    Epi ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A X n)).app (op ⊤)) :=
  (ModuleCat.epi_iff_surjective _).2
    (singularCochain_sheafification_top_surjective_of_paracompact A X n)

end

end OAI.AlgebraicTopology.Cohomology.Singular.ParacompactSheafificationRepresentatives
