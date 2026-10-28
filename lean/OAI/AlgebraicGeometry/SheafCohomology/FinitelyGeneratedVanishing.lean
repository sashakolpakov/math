import OAI.AlgebraicGeometry.SheafCohomology.VanishingPresheafFilteredG
import OAI.AlgebraicGeometry.SheafCohomology.ClosedImmersionCohomology
import OAI.AlgebraicGeometry.SheafCohomology.GeneratedSubsheaf

/-! # Finitely Generated Vanishing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.FinitelyGeneratedVanishing

open _root_.CategoryTheory _root_.TopologicalSpace _root_.Order
open _root_.CategoryTheory.Limits _root_.Opposite

set_option backward.isDefEq.respectTransparency false

namespace Projective

open OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat

/-!
# Finitely generated vanishing reduction

On a Noetherian space, every sheaf is the filtered colimit of its finitely generated
subsheaves, and sheaf cohomology commutes with filtered colimits. Combining the two
reduces vanishing of `Hⁿ` for arbitrary sheaves to vanishing for finitely generated ones.
This file packages that reduction; together with the Noetherian-shrinking step, it
underlies the irreducible positive-dimensional case of Grothendieck vanishing.

## Main definitions

* `finsetGenFunctor` — the filtered diagram of finitely generated subsheaves.
* `finsetGenCocone`, `finsetGenCocone_isColimit` — exhibits `K` as the colimit.

## Main results

* `cohomology_vanishing_of_finitelyGenerated_vanishing` — vanishing for f.g. subsheaves
 propagates to the whole sheaf via the filtered-colimit comparison.
* `finsetGeneratedSheaf_vanishing` — `Finset.induction` reducing vanishing for finitely
 generated subsheaves to vanishing for the epi-images of `zeroOutsideInt V`.
* `directLimit_cohomology_vanishing` — composes both above into the headline reduction.

The `isFlasque_filtered_colimit` and `sheafH_preserves_filtered_colimits` building blocks
live in the `PresheafFilteredColimit` modules.
-/

universe u

open Abelian Limits

/-! ### Filtered diagram of finitely generated subsheaves

We build a functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending each finite set `S`
of local sections to the subsheaf `finsetGeneratedSheaf S`. The transition maps
(for `S ⊆ S'`) are monomorphisms, and K is the colimit of this filtered diagram. -/

section FilteredDiagram
open scoped Classical

variable {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)

/-- The functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending `S ↦ finsetGeneratedSheaf S`.
 Transition maps are the canonical image inclusions, which are monomorphisms. -/
noncomputable def finsetGenFunctor :
    Finset
        (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.SectionIndex K) ⥤
      Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X where
  obj S := GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratedSheaf hK S
  map h := GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetImageInclGen hK h.le
  map_id S := by
    apply (cancel_mono (Limits.image.ι (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratorMap hK S))).1
    rw [GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetImageInclGen_comp_ι, Category.id_comp]
  map_comp {S₁ S₂ S₃} h₁ h₂ := by
    apply (cancel_mono (Limits.image.ι (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratorMap hK S₃))).1
    rw [Category.assoc, GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetImageInclGen_comp_ι,
      GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetImageInclGen_comp_ι,
      GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetImageInclGen_comp_ι]

/-- Cocone with vertex `K`: the cocone maps are `image.ι: finsetGeneratedSheaf S ⟶ K`. -/
noncomputable def finsetGenCocone :
    Cocone (finsetGenFunctor hK) :=
  Cocone.mk (⟨K, hK⟩ : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X)
    { app := fun S ↦ Limits.image.ι (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratorMap hK S)
      naturality := fun S S' h ↦ by
        simp [finsetGenFunctor, GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetImageInclGen_comp_ι] }

/-- The cocone is a colimit: `K` is the filtered colimit of its finitely generated subsheaves.
 Proof: the canonical map `colim → K` is mono (by AB5 + mono transitions) and epi
 (since `allSectionMap K` factors through it), hence an isomorphism. -/
noncomputable def finsetGenCocone_isColimit :
    IsColimit (finsetGenCocone hK) := by
  -- Show the comparison map colim → K is an iso, then transport IsColimit
  let d := colimit.desc (finsetGenFunctor hK) (finsetGenCocone hK)
  -- desc is mono: natural transformation to const K has all components mono (image.ι),
  -- and in a Grothendieck abelian category filtered colimits preserve monos
  have hd_mono : Mono d := by
    have : IsConnected
        (Finset (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.SectionIndex K)) := IsFiltered.isConnected _
    have : ∀ j, Mono ((finsetGenCocone hK).ι.app j) := fun j ↦
      show Mono (Limits.image.ι (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratorMap hK j)) from inferInstance
    have := NatTrans.mono_of_mono_app (finsetGenCocone hK).ι
    exact colim.map_mono' (finsetGenCocone hK).ι (colimit.isColimit _)
      (isColimitConstCocone _ _) d (fun j ↦ by simp [d, finsetGenCocone, constCocone])
  -- desc is epi: allSectionMap K factors through desc
  have hd_epi : Epi d := by
    let g : (∐ fun σ : GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.SectionIndex K ↦ Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt σ.1) ⟶
        colimit (finsetGenFunctor hK) :=
      Sigma.desc fun σ ↦
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} ↦
            Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
          factorThruImage (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
          colimit.ι (finsetGenFunctor hK) {σ}
    have hfac : g ≫ d = GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.allSectionMap hK := by
      ext σ
      dsimp only [g, d]
      rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc, Category.assoc, colimit.ι_desc]
      simp [finsetGenCocone, GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.allSectionMap,
        GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratorMap, Vanishing.Projective.TopCat.Sheaf.familyMap]
    have := GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.allSectionMap_epi (F := K) hK
    exact epi_of_epi_fac hfac
  -- mono + epi → iso in abelian category
  have : Mono d := hd_mono
  have : Epi d := hd_epi
  have : IsIso ((colimit.isColimit (finsetGenFunctor hK)).desc (finsetGenCocone hK)) :=
    isIso_of_mono_of_epi d
  exact (colimit.isColimit (finsetGenFunctor hK)).ofPointIso

end FilteredDiagram

/-- **Hartshorne III, Ex. 2.9 core**: on a Noetherian space, if `H^m = 0` for all finitely generated
 subsheaves of `K`, then `H^m(K) = 0`. Uses the filtered-colimit comparison isomorphism
 for the diagram of finitely generated subsheaves and transports zero across it. -/
theorem cohomology_vanishing_of_finitelyGenerated_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf) (m : ℕ)
    (hfg : ∀ (S : Finset
        (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.SectionIndex K))
      [HasCoproduct fun σ : {σ // σ ∈ S} ↦ Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt σ.1.1],
      Subsingleton (Sheaf.H (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratedSheaf hK S) m)) :
    Subsingleton (Sheaf.H (⟨K, hK⟩ : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) m) := by
  have hZeroDiagram : IsZero (finsetGenFunctor hK ⋙ API.ProjectiveVanishing.sheafCohomologyFunctor X m) := by
    refine Functor.isZero _ ?_
    intro S
    have : Subsingleton (Sheaf.H (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratedSheaf hK S) m) := hfg S
    exact
      (AddCommGrpCat.isZero_of_subsingleton
        (AddCommGrpCat.of (Sheaf.H (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratedSheaf hK S) m)))
  have hZeroColim :
      IsZero (colimit (finsetGenFunctor hK ⋙ API.ProjectiveVanishing.sheafCohomologyFunctor X m)) :=
    (colimit.isColimit _).isZero_pt hZeroDiagram
  have hZeroTarget :
      IsZero (AddCommGrpCat.of
        (Sheaf.H (⟨K, hK⟩ : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) m)) := by
    simpa [finsetGenCocone] using
      IsZero.of_iso hZeroColim
        (VanishingPresheafFilteredG.Projective.sheafH_preserves_filtered_colimits
          (Y' := finsetGenFunctor hK)
          (c' := finsetGenCocone hK)
          (hc' := finsetGenCocone_isColimit hK)
          m).symm
  simpa using AddCommGrpCat.subsingleton_of_isZero hZeroTarget

section FinsetGenerated
open scoped Classical

variable {X : TopCat.{u}} {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)

/-- **Step 3B–3C**: vanishing for `finsetGeneratedSheaf S` by `Finset.induction`. -/
theorem finsetGeneratedSheaf_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)
    (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt V).obj ⟶ G),
      TopCat.Presheaf.IsLocallySurjective f →
      Subsingleton (Sheaf.H (⟨G, hG⟩ : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) m))
    (S : Finset
      (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.SectionIndex K))
    [HasCoproduct fun σ : {σ // σ ∈ S} ↦ Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Subsingleton (Sheaf.H (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratedSheaf hK S) m) := by
  suffices h : ∀ (T : Finset (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.SectionIndex K)),
      Subsingleton (Sheaf.H (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratedSheaf hK T) m) from h S
  intro T; induction T using Finset.induction with
  | empty =>
    exact API.ProjectiveVanishing.sheafH_subsingleton_of_isZero
      (IsZero.of_iso (isZero_zero _) (imageZero' (by
        ext ⟨σ, hσ⟩
        simp at hσ))) m
  | @insert σ₀ S' _ ih =>
    let h_sub := Finset.subset_insert σ₀ S'
    let f := GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetImageInclGen hK h_sub
    let qIns := factorThruImage (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S'))
    let qS := factorThruImage (GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetGeneratorMap hK S')
    let g : Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt σ₀.1 ⟶ cokernel f :=
      Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} ↦ Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt σ.1.1)
        ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫ qIns ≫ cokernel.π f
    have : Epi g := by
      refine epi_of_epi_fac
        (f := Sigma.desc fun σ ↦ if h : σ.1 = σ₀ then eqToHom (by rw [h]) else 0)
        (h := qIns ≫ cokernel.π f) ?_
      apply Sigma.hom_ext
      intro ⟨σ, hσ⟩
      by_cases h : σ = σ₀
      · subst h
        simp [g]
      · simpa [g, GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetCoproductInclGen, Category.assoc, h,
          cokernel.condition] using
          (congrArg (fun e ↦ Sigma.ι
            (fun τ : {τ // τ ∈ S'} ↦ Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt τ.1.1)
            ⟨σ, Finset.mem_of_mem_insert_of_ne hσ h⟩ ≫ e ≫ cokernel.π f)
            (show GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetCoproductInclGen h_sub ≫ qIns = qS ≫ f by
              simp [qIns, qS, f, GeneratedSubsheaf.ProjectiveVanishing.TopCat.Presheaf.finsetImageInclGen])).symm
    exact API.ProjectiveVanishing.subsingleton_sheafH_of_shortExact_middle f m ih <|
      hzero (cokernel f).property g.hom
        ((Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} g).mpr inferInstance)

end FinsetGenerated

/-- **Step 3A** (Hartshorne III.2.7): on a Noetherian space, if vanishing holds for
 all epi images of `zeroOutsideInt V`, then it holds for every sheaf.
 Assembles `finsetGeneratedSheaf_vanishing` (finite case) with
 `cohomology_vanishing_of_finitelyGenerated_vanishing` (colimit step). -/
theorem directLimit_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf) (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : (Vanishing.Projective.TopCat.Sheaf.zeroOutsideInt V).obj ⟶ G),
      TopCat.Presheaf.IsLocallySurjective f →
      Subsingleton (Sheaf.H (⟨G, hG⟩ : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) m)) :
    Subsingleton (Sheaf.H (⟨K, hK⟩ : Vanishing.Projective.TopCat.Sheaf AddCommGrpCat.{u} X) m) := by
  exact cohomology_vanishing_of_finitelyGenerated_vanishing hK m
    (fun S _ ↦ finsetGeneratedSheaf_vanishing hK m hzero S)
end Projective

end OAI.AlgebraicGeometry.SheafCohomology.FinitelyGeneratedVanishing
