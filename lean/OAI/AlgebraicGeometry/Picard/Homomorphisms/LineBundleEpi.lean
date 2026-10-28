import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.PicardGroup

/-! # Line Bundle Epi -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleEpi

noncomputable section

/-!
# Homomorphisms: epimorphisms between line bundles are isomorphisms

On affine trivializing opens, the assertion reduces through the fully
faithful tilde functor to a surjective map between free rank-one modules.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem unit_spec_epi_isIso (R : CommRingCat.{u})
    (f : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec R) ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec R)) [Epi f] : IsIso f := by
  let e := tildeSelf (R := R)
  let g := (tilde.fullyFaithfulFunctor (R := R)).preimage (e.hom ≫ f ≫ e.inv)
  have hg : (tilde.functor R).map g = e.hom ≫ f ≫ e.inv :=
    (tilde.fullyFaithfulFunctor (R := R)).map_preimage _
  have he : e.hom ≫ f ≫ e.inv = f := by
    change (𝟙 _) ≫ f ≫ (𝟙 _) = f
    rw [Category.id_comp, Category.comp_id]
  have hge : Epi ((tilde.functor R).map g) := (hg.trans he).symm ▸ inferInstanceAs (Epi f)
  have : Epi g := (tilde.functor R).epi_of_epi_map hge
  have hgBij : Function.Bijective g.hom :=
    Module.Invertible.bijective_of_surjective ((ModuleCat.epi_iff_surjective g).mp inferInstance)
  have : IsIso g := (ConcreteCategory.isIso_iff_bijective g).mpr hgBij
  exact (hg.trans he) ▸ inferInstanceAs (IsIso ((tilde.functor R).map g))

def moduleFrameRestrict {X : Scheme.{u}} (L : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    (Scheme.Modules.pullback V.ι).obj L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule V.toScheme :=
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι h).symm).app L ≪≫
    (Scheme.Modules.pullbackComp (X.homOfLE h) U.ι).symm.app L ≪≫
    (Scheme.Modules.pullback (X.homOfLE h)).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (X.homOfLE h)

theorem lineBundle_epi_locally_injective {X : Scheme.{u}} (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (f : L.sheaf ⟶ M.sheaf) [Epi f] (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, V ≤ U ∧ x ∈ V ∧ Function.Injective (f.app V) := by
  obtain ⟨U₁, hx₁, ⟨e₁⟩⟩ := L.locallyTrivial x
  obtain ⟨U₂, hx₂, ⟨e₂⟩⟩ := M.locallyTrivial x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U ⊓ (U₁ ⊓ U₂) from ⟨hx, hx₁, hx₂⟩)
  have : IsAffine V.toScheme := hV
  let a := V.toScheme.isoSpec.inv ≫ V.ι
  let l : (Scheme.Modules.pullback a).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (CommRingCat.of Γ(V.toScheme, ⊤))) :=
    (Scheme.Modules.pullbackComp V.toScheme.isoSpec.inv V.ι).symm.app L.sheaf ≪≫
      (Scheme.Modules.pullback V.toScheme.isoSpec.inv).mapIso
        (moduleFrameRestrict L.sheaf (hVU.trans (inf_le_right.trans inf_le_left)) e₁) ≪≫
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso V.toScheme.isoSpec.inv
  let m : (Scheme.Modules.pullback a).obj M.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (CommRingCat.of Γ(V.toScheme, ⊤))) :=
    (Scheme.Modules.pullbackComp V.toScheme.isoSpec.inv V.ι).symm.app M.sheaf ≪≫
      (Scheme.Modules.pullback V.toScheme.isoSpec.inv).mapIso
        (moduleFrameRestrict M.sheaf (hVU.trans (inf_le_right.trans inf_le_right)) e₂) ≪≫
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso V.toScheme.isoSpec.inv
  have hu : IsIso (l.inv ≫ (Scheme.Modules.pullback a).map f ≫ m.hom) :=
    unit_spec_epi_isIso _ _
  have hi : IsIso ((Scheme.Modules.pullback a).map f) := by
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hu
  let e := Scheme.Modules.restrictFunctorIsoPullback a
  have hj : IsIso ((Scheme.Modules.restrictFunctor a).map f ≫ e.hom.app M.sheaf) := by
    erw [e.hom.naturality f]
    infer_instance
  have : IsIso ((Scheme.Modules.restrictFunctor a).map f) :=
    (isIso_comp_right_iff _ (e.hom.app M.sheaf)).mp hj
  have ht : IsIso (f.app (a ''ᵁ ⊤)) :=
    inferInstanceAs (IsIso (((Scheme.Modules.restrictFunctor a).map f).app ⊤))
  have ha : a ''ᵁ ⊤ = V := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp,
      Scheme.Hom.opensRange_of_isIso, Scheme.Opens.ι_image_top]
  have ht' : IsIso (f.app V) := ha ▸ ht
  exact ⟨V, hVU.trans inf_le_left, hxV, (ConcreteCategory.bijective_of_isIso (f.app V)).injective⟩

theorem lineBundle_epi_isIso {X : Scheme.{u}} (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (f : L.sheaf ⟶ M.sheaf) [Epi f] : IsIso f := by
  have hinj (U : X.Opens) : Function.Injective (f.app U) := by
    intro s t h
    apply L.sheaf.isSheaf.section_ext
    intro x hx
    obtain ⟨V, hVU, hxV, hV⟩ := lineBundle_epi_locally_injective L M f U x hx
    refine ⟨V, hVU, hxV, hV ?_⟩
    have hn (s : Γ(L.sheaf, U)) :=
      PresheafOfModules.naturality_apply f.val (homOfLE hVU).op s
    exact (hn s).trans ((congrArg (M.sheaf.presheaf.map (homOfLE hVU).op) h).trans (hn t).symm)
  have : Mono f := {
    right_cancellation := fun g h e => by
      apply Scheme.Modules.hom_ext
      intro U
      apply ConcreteCategory.hom_ext
      intro s
      apply hinj U
      exact ConcreteCategory.congr_hom (congrArg (fun k => k.app U) e) s }
  exact isIso_of_mono_of_epi f

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleEpi
