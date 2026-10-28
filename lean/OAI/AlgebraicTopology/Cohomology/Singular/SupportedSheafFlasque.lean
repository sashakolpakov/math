import OAI.AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport

/-! # Supported Sheaf Flasque -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SupportedSheafFlasque

noncomputable section

/-!
# Flasqueness of the genuine sheaf of sections with closed support

A section vanishing on the intersection with an open complement glues with
zero on that complement. Flasqueness then extends the gluing to the whole
space, still with the prescribed support. This proves flasqueness for the
actual kernel sheaf of sections supported in a closed subset.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] {X : TopCat.{0}}

/-- A local section of a flasque module sheaf that vanishes on an open
complement extends globally while continuing to vanish there. -/
theorem exists_global_extension_vanishing_on_open
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) [TopCat.Sheaf.IsFlasque F]
    (U O : Opens X) (s : F.obj.obj (op U))
    (hs : F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op s = 0) :
    ∃ t : F.obj.obj (op (⊤ : Opens X)),
      F.obj.map (homOfLE (le_top : U ≤ ⊤)).op t = s ∧
        F.obj.map (homOfLE (le_top : O ≤ ⊤)).op t = 0 := by
  let W : Fin 2 → Opens X := ![U, O]
  let sW : (i : Fin 2) → F.obj.obj (op (W i))
    | 0 => s
    | 1 => 0
  have hcompat : TopCat.Presheaf.IsCompatible F.obj W sW := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · change (F.obj.map (homOfLE (inf_le_left : U ⊓ O ≤ U)).op).hom s =
        (F.obj.map (homOfLE (inf_le_right : U ⊓ O ≤ O)).op).hom 0
      rw [map_zero]
      exact hs
    · change (F.obj.map (homOfLE (inf_le_left : O ⊓ U ≤ O)).op).hom 0 =
        (F.obj.map (homOfLE (inf_le_right : O ⊓ U ≤ U)).op).hom s
      rw [map_zero]
      let k : O ⊓ U ⟶ U ⊓ O := homOfLE (le_of_eq (inf_comm O U))
      have hs' := congrArg (F.obj.map k.op).hom hs
      rw [map_zero, ← ConcreteCategory.comp_apply, ← F.obj.map_comp] at hs'
      exact hs'.symm
    · rfl
  obtain ⟨t, ht, _⟩ := F.existsUnique_gluing W sW hcompat
  obtain ⟨g, hg⟩ := (ModuleCat.epi_iff_surjective
    (F.obj.map (homOfLE (le_top : iSup W ≤ ⊤)).op)).mp inferInstance t
  refine ⟨g, ?_, ?_⟩
  · calc
      F.obj.map (homOfLE (le_top : U ≤ ⊤)).op g =
          F.obj.map (Opens.leSupr W 0).op
            (F.obj.map (homOfLE (le_top : iSup W ≤ ⊤)).op g) := by
              rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
              rfl
      _ = F.obj.map (Opens.leSupr W 0).op t := congrArg _ hg
      _ = s := ht 0
  · calc
      F.obj.map (homOfLE (le_top : O ≤ ⊤)).op g =
          F.obj.map (Opens.leSupr W 1).op
            (F.obj.map (homOfLE (le_top : iSup W ≤ ⊤)).op g) := by
              rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
              rfl
      _ = F.obj.map (Opens.leSupr W 1).op t := congrArg _ hg
      _ = 0 := ht 1

/-- Every section of the actual closed-support kernel sheaf extends to a
global section of the same kernel sheaf. -/
theorem closedSupportSheaf_top_restriction_surjective (O U : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) [TopCat.Sheaf.IsFlasque F] :
    Function.Surjective ((AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F).obj.map
      (homOfLE (le_top : U ≤ ⊤)).op) := by
  intro s
  obtain ⟨g, hgU, hgO⟩ := exists_global_extension_vanishing_on_open F U O
    ((AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F).hom.app (op U) s)
    (AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_vanishes O U F s)
  have hgker : g ∈ LinearMap.ker
      ((F.obj.map (homOfLE (inf_le_left : (⊤ : Opens X) ⊓ O ≤ ⊤)).op).hom) := by
    change F.obj.map (homOfLE (inf_le_left : (⊤ : Opens X) ⊓ O ≤ ⊤)).op g = 0
    have hz := congrArg
      (F.obj.map (homOfLE (inf_le_right : (⊤ : Opens X) ⊓ O ≤ O)).op).hom hgO
    rw [map_zero, ← ConcreteCategory.comp_apply, ← F.obj.map_comp] at hz
    exact hz
  rw [← AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_range O ⊤ F] at hgker
  obtain ⟨t, ht⟩ := hgker
  refine ⟨t, ?_⟩
  apply AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion_injective O U F
  rw [← ConcreteCategory.comp_apply,
    (AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O F).hom.naturality,
    ConcreteCategory.comp_apply, ht]
  exact hgU

/-- Restriction of sections with the prescribed closed support is surjective
for every inclusion of open sets. -/
theorem closedSupportSheaf_restriction_surjective (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) [TopCat.Sheaf.IsFlasque F]
    {U V : Opens X} (i : U ⟶ V) :
    Function.Surjective ((AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F).obj.map i.op) := by
  intro s
  obtain ⟨t, ht⟩ := closedSupportSheaf_top_restriction_surjective O U F s
  refine ⟨(AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F).obj.map (homOfLE (le_top : V ≤ ⊤)).op t, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← (AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F).obj.map_comp]
  exact ht

/-- The genuine sheaf of sections with closed support of a flasque module
sheaf is flasque. -/
instance closedSupportSheaf_isFlasque (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque (AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F) where
  epi i := (ModuleCat.epi_iff_surjective _).mpr
    (closedSupportSheaf_restriction_surjective O F i.unop)

/-- The same actual supported sheaf remains flasque after forgetting its
module structure to abelian groups. -/
theorem closedSupportSheaf_forget_isFlasque (O : Opens X)
    (F : TopCat.Sheaf (ModuleCat.{0} R) X) [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ (ModuleCat.{0} R) AddCommGrpCat.{0})).obj (AlgebraicGeometry.CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheaf O F)) where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (closedSupportSheaf_restriction_surjective O F i.unop)

end

end OAI.AlgebraicTopology.Cohomology.Singular.SupportedSheafFlasque
