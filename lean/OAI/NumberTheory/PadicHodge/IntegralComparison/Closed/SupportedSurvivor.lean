import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ComplementAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionIdealPuncturedCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ZeroComplementComplex

/-! # Supported Survivor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.SupportedSurvivor

noncomputable section

/-! A genuine closed direct image, or an isomorphic surviving
cohomology sheaf, has canonical supported extension from every open
containing the closed subscheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

theorem preimage_outside : f ⁻¹ᵁ SectionIdealPuncturedCover.outside f.ker = ⊥ := by
  apply le_antisymm
  · intro x hx
    change f x ∉ f.ker.support at hx
    exact False.elim (hx (by
      change f x ∈ (f.ker.support : Set Y)
      rw [Scheme.Hom.support_ker]
      exact subset_closure ⟨x, rfl⟩))
  · exact bot_le

theorem outside_kernel : RingHom.ker
    (f.app (SectionIdealPuncturedCover.outside f.ker)).hom = ⊤ := by
  let : Subsingleton Γ(X, f ⁻¹ᵁ SectionIdealPuncturedCover.outside f.ker) := by
    rw [preimage_outside]
    infer_instance
  apply Ideal.eq_top_of_isUnit_mem _ (x := 1) _ isUnit_one
  change f.app _ 1 = 0
  exact Subsingleton.elim _ _

variable (N : X.Modules) (S : Y.Modules) (e : S ≅ (Scheme.Modules.pushforward f).obj N)

abbrev sheaf := (SheafOfModules.toSheaf Y.ringCatSheaf).obj S

include N e in
theorem sections_zero : IsZero ((sheaf S).obj.obj
    (op (SectionIdealPuncturedCover.outside f.ker))) := by
  have hz := Projective.ComplementAdjunction.directImage_sections_zero f N
    (SectionIdealPuncturedCover.outside f.ker) (outside_kernel f)
  have hz' := (forget₂ (ModuleCat Γ(Y, SectionIdealPuncturedCover.outside f.ker)) AddCommGrpCat).map_isZero hz
  exact hz'.of_iso
    (((CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat).obj
      (op (SectionIdealPuncturedCover.outside f.ker))).mapIso
        ((sheafToPresheaf _ _).mapIso ((SheafOfModules.toSheaf Y.ringCatSheaf).mapIso e)))

abbrev single (c : ℕ) := (HomologicalComplex.single
  (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (.up ℕ) c).obj (sheaf S)

include N e in
theorem terms_zero (c q : ℕ) : IsZero (((SupportedSurvivor.single S c).X q).obj.obj
    (op (SectionIdealPuncturedCover.outside f.ker))) := by
  let E := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat).obj
      (op (SectionIdealPuncturedCover.outside f.ker))
  by_cases hq : q = c
  · subst q
    exact (sections_zero f N S e).of_iso (E.mapIso (singleObjXSelf (.up ℕ) c (sheaf S)))
  · exact E.map_isZero (isZero_single_obj_X (.up ℕ) c (sheaf S) q hq)

variable (U : Y.Opens) (hU : ⊤ ≤ f ⁻¹ᵁ U) (c : ℕ)

abbrev lift := Supported.ZeroComplementComplex.lift
  (SectionIdealPuncturedCover.outside f.ker) U (SupportedSurvivor.single S c) (terms_zero f N S e c)

abbrev homology_extension (q : ℕ) := Supported.ZeroComplementComplex.homology_extension
  (SectionIdealPuncturedCover.outside f.ker) U
    (SectionIdealPuncturedCover.section_global U f hU) (SupportedSurvivor.single S c) (terms_zero f N S e c) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.SupportedSurvivor
