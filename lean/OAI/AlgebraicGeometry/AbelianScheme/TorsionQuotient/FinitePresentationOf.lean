import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Finite Presentation Of -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FinitePresentationOf.FinitePresentation

/-!
# TorsionQuotient: finite presentation of the multiplication morphism

If a composite is locally of finite presentation and its second morphism
is locally of finite type, the first morphism is locally of finite
presentation. The proof is the algebraic cancellation theorem on affine
neighborhoods of each source point.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := by
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation)
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FinitePresentation)
  let : MorphismProperty.RespectsRight (@LocallyOfFinitePresentation.{u}) @IsOpenImmersion :=
    { postcomp := fun {X Y Z} g hg f hf => by
        let : IsOpenImmersion g := hg
        let : LocallyOfFinitePresentation f := hf
        exact locallyOfFinitePresentation_comp f g }
  refine (IsZariskiLocalAtSource.iff_exists_resLE
    (P := @LocallyOfFinitePresentation) (f := f)).mpr ?_
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f x))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ g ⁻¹ᵁ U⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxU (g ⁻¹ᵁ U).isOpen
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV : W ≤ f ⁻¹ᵁ V⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
  have hWU : W ≤ (f ≫ g) ⁻¹ᵁ U := hWV.trans (f.preimage_mono hVU)
  have hcomp : ((f.appLE V W hWV).hom.comp (g.appLE U V hVU).hom).FinitePresentation := by
    change (g.appLE U V hVU ≫ f.appLE V W hWV).hom.FinitePresentation
    rw [Scheme.Hom.appLE_comp_appLE]
    exact (f ≫ g).finitePresentation_appLE hU hW hWU
  have hfp := RingHom.FinitePresentation.of_comp_finiteType (g.appLE U V hVU).hom hcomp
    (g.finiteType_appLE hU hV hVU)
  refine ⟨V, W, hxW, hWV, ?_⟩
  let : IsAffine (Scheme.Opens.toScheme V) := hV
  let : IsAffine (Scheme.Opens.toScheme W) := hW
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  exact (RingHom.finitePresentation_isLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f V W hWV)).mpr hfp

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FinitePresentationOf.FinitePresentation
