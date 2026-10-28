import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedLifts
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Pointed Lifts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PointedLifts

noncomputable section

/-! Pointed unramified lifts are unique over any base when the source
has geometrically connected fibers. The equality locus is open and closed,
and the common section meets every fiber. No connectedness or reducedness
of the base is required. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem clopen_eq_univ_of_connected_fibers_and_section
    {X B : Type*} [TopologicalSpace X] (p : X → B) (s : B → X)
    (hs : Function.RightInverse s p) (hconn : ∀ b, IsConnected (p ⁻¹' {b}))
    {U : Set X} (hU : IsClopen U) (hsec : Set.range s ⊆ U) : U = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let F := {y : X // p y = p x}
  have : ConnectedSpace F := isConnected_iff_connectedSpace.mp (hconn (p x))
  have hc : IsClopen ((Subtype.val : F → X) ⁻¹' U) := hU.preimage continuous_subtype_val
  have hn : ((Subtype.val : F → X) ⁻¹' U).Nonempty :=
    ⟨⟨s (p x), hs (p x)⟩, hsec (Set.mem_range_self _)⟩
  have heq := hc.eq_univ hn
  have hmem : (⟨x, rfl⟩ : F) ∈ (Subtype.val : F → X) ⁻¹' U := by rw [heq]; trivial
  exact hmem

theorem relative_pointed_unramified_lifts_unique
    {B X Y Z : Scheme} (pX : X ⟶ B) [GeometricallyConnected pX]
    (s : B ⟶ X) (hs : s ≫ pX = 𝟙 B)
    (q : Y ⟶ Z) [FormallyUnramified q] [LocallyOfFiniteType q] [IsSeparated q]
    (f g : X ⟶ Y) (hcomp : f ≫ q = g ≫ q)
    (hpoint : s ≫ f = s ≫ g) : f = g := by
  let p : X ⟶ pullback q q := pullback.lift f g hcomp
  let d := pullback.diagonal q
  let E := pullback p d
  let e : E ⟶ X := pullback.fst p d
  have hpoint' : s ≫ p = (s ≫ f) ≫ d := by
    apply pullback.hom_ext
    · simp only [Category.assoc, p, d, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [Category.assoc, p, d, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
      exact hpoint.symm
  let z : B ⟶ E := pullback.lift s (s ≫ f) hpoint'
  have : IsOpenImmersion e := inferInstanceAs (IsOpenImmersion (pullback.fst p d))
  have : IsClosedImmersion e := inferInstanceAs (IsClosedImmersion (pullback.fst p d))
  have he : IsClopen (Set.range e) := ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩
  have hsection : Function.RightInverse s pX := fun b => congrArg (fun m : B ⟶ B => m b) hs
  have hsec : Set.range s ⊆ Set.range e := by
    rintro _ ⟨b, rfl⟩
    exact ⟨z b, congrArg (fun m : B ⟶ X => m b) (pullback.lift_fst _ _ _)⟩
  have hrange : Set.range e = Set.univ := clopen_eq_univ_of_connected_fibers_and_section
    pX s hsection pX.isConnected_preimage_singleton he hsec
  have : Surjective e := ⟨Set.range_eq_univ.mp hrange⟩
  have : IsIso e := (isIso_iff_isOpenImmersion_and_surjective e).mpr ⟨inferInstance, inferInstance⟩
  have h : e ≫ p = pullback.snd p d ≫ d := pullback.condition
  have hf : e ≫ f = pullback.snd p d := by
    simpa only [Category.assoc, p, d, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      using congrArg (fun k => k ≫ pullback.fst q q) h
  have hg : e ≫ g = pullback.snd p d := by
    simpa only [Category.assoc, p, d, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
      using congrArg (fun k => k ≫ pullback.snd q q) h
  exact (cancel_epi e).mp (hf.trans hg.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PointedLifts
