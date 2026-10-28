import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Source Property Open Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SourcePropertyOpenLocus

noncomputable section

/-! Every morphism property local on the source has a largest open source locus on which it holds. This supplies the source locus for a specified smooth relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
variable {X S : Scheme.{u}} (f : X ⟶ S)

def sourcePropertyOpenLocus : X.Opens := ⨆ U : {U : X.Opens // P (U.ι ≫ f)}, U.val

omit [IsZariskiLocalAtSource P] in
theorem le_sourcePropertyOpenLocus (U : X.Opens) (hU : P (U.ι ≫ f)) : U ≤ sourcePropertyOpenLocus P f :=
  le_iSup (fun V : {V : X.Opens // P (V.ι ≫ f)} => V.val) ⟨U, hU⟩

theorem sourcePropertyOpenLocus_property : P ((sourcePropertyOpenLocus P f).ι ≫ f) := by
  let V := sourcePropertyOpenLocus P f
  let W (U : {U : X.Opens // P (U.ι ≫ f)}) : V.toScheme.Opens := V.ι ⁻¹ᵁ U.val
  have hW : (⨆ U, W U) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨U, hx⟩ := (Opens.mem_iSup).mp x.property
    exact (Opens.mem_iSup).mpr ⟨U, hx⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := P) W hW
  intro U
  have : IsOpenImmersion (V.ι.resLE U.val (W U) le_rfl) := by
    dsimp only [Scheme.Hom.resLE]
    infer_instance
  have hr : P (V.ι.resLE U.val (W U) le_rfl ≫ U.val.ι ≫ f) :=
    IsZariskiLocalAtSource.comp U.property (V.ι.resLE U.val (W U) le_rfl)
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc] at hr
  exact hr

theorem sourcePropertyOpenLocus_iff (U : X.Opens) : P (U.ι ≫ f) ↔ U ≤ sourcePropertyOpenLocus P f := by
  refine ⟨le_sourcePropertyOpenLocus P f U, fun hU => ?_⟩
  have h := IsZariskiLocalAtSource.comp (sourcePropertyOpenLocus_property P f) (X.homOfLE hU)
  rwa [← Category.assoc, Scheme.homOfLE_ι] at h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SourcePropertyOpenLocus
