import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.CoverIntersections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonoFamilyGluing
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MorphismFactorization

/-! # Cover Gluing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.CoverGluing

noncomputable section

/-! Compatible closed subschemes on ambient open pieces glue to a scheme.
Its restriction to every given ambient piece is the specified closed subscheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {J : Type u} (V Z : J → Scheme.{u})
variable (u : ∀ i, V i ⟶ X) (c : ∀ i, Z i ⟶ V i)
variable [∀ i, IsOpenImmersion (u i)] [∀ i, IsClosedImmersion (c i)]
variable (hc : ∀ i j, (c i).ker.comap (pullback.fst (u i) (u j)) =
  (c j).ker.comap (pullback.snd (u i) (u j)))

def closedCoverGlueData : Scheme.GlueData := by
  let : ∀ i j, IsOpenImmersion (pullback.fst (CoverIntersections.closedCoverMap V Z u c i) (CoverIntersections.closedCoverMap V Z u c j)) :=
    CoverIntersections.closedCoverIntersection_fst_isOpenImmersion V Z u c hc
  exact MonoFamilyGluing.schemeMonoFamilyGlueData Z (CoverIntersections.closedCoverMap V Z u c)

def closedCoverParameter : (closedCoverGlueData V Z u c hc).glued ⟶ X := by
  let : ∀ i j, IsOpenImmersion (pullback.fst (CoverIntersections.closedCoverMap V Z u c i) (CoverIntersections.closedCoverMap V Z u c j)) :=
    CoverIntersections.closedCoverIntersection_fst_isOpenImmersion V Z u c hc
  exact MonoFamilyGluing.schemeMonoFamilyParameter Z (CoverIntersections.closedCoverMap V Z u c)

@[reassoc]
theorem closedCoverChart_parameter (i : J) :
    (closedCoverGlueData V Z u c hc).ι i ≫ closedCoverParameter V Z u c hc = c i ≫ u i := by
  let : ∀ i j, IsOpenImmersion (pullback.fst (CoverIntersections.closedCoverMap V Z u c i) (CoverIntersections.closedCoverMap V Z u c j)) :=
    CoverIntersections.closedCoverIntersection_fst_isOpenImmersion V Z u c hc
  exact MonoFamilyGluing.schemeMonoFamilyChart_parameter Z (CoverIntersections.closedCoverMap V Z u c) i

instance closedCoverParameter_mono : Mono (closedCoverParameter V Z u c hc) := by
  let : ∀ i j, IsOpenImmersion (pullback.fst (CoverIntersections.closedCoverMap V Z u c i) (CoverIntersections.closedCoverMap V Z u c j)) :=
    CoverIntersections.closedCoverIntersection_fst_isOpenImmersion V Z u c hc
  exact MonoFamilyGluing.schemeMonoFamilyParameter_mono Z (CoverIntersections.closedCoverMap V Z u c)

theorem closedCoverChart_isPullback (i : J) :
    IsPullback (c i) ((closedCoverGlueData V Z u c hc).ι i) (u i) (closedCoverParameter V Z u c hc) := by
  let D := closedCoverGlueData V Z u c hc
  let p : D.glued ⟶ X := closedCoverParameter V Z u c hc
  change IsPullback (c i) (D.ι i) (u i) p
  apply IsPullback.mk'
  · exact (closedCoverChart_parameter V Z u c hc i).symm
  · intro W f g h _
    exact (cancel_mono (c i)).mp h
  · intro W a b h
    let A := D.openCover.pullback₁ b
    have hloc : ∀ j, ∃ l : A.X j ⟶ Z i, l ≫ c i = A.f j ≫ a := by
      intro j
      change J at j
      let z : A.X j ⟶ Z j := D.openCover.pullbackHom b j
      have hz : z ≫ D.ι j = A.f j ≫ b := D.openCover.pullbackHom_map b j
      have hj : D.ι j ≫ p = c j ≫ u j := closedCoverChart_parameter V Z u c hc j
      have he : z ≫ c j ≫ u j = (A.f j ≫ a) ≫ u i := by
        calc
          _ = z ≫ (D.ι j ≫ p) := congrArg (fun l => z ≫ l) hj.symm
          _ = (z ≫ D.ι j) ≫ p := (Category.assoc _ _ _).symm
          _ = (A.f j ≫ b) ≫ p := congrArg (fun l => l ≫ p) hz
          _ = _ := by simpa only [Category.assoc] using congrArg (fun l => A.f j ≫ l) h.symm
      exact ImmersionOverlapLifts.closedImmersion_overlap_lift (u j) (u i) (c j) (c i) (hc j i) z (A.f j ≫ a) he
    obtain ⟨l, hl, _⟩ := Local.MorphismFactorization.lift_of_openCover A a (c i) hloc
    refine ⟨l, hl, ?_⟩
    apply (cancel_mono p).mp
    have hi : (D.ι i : Z i ⟶ D.glued) ≫ p = c i ≫ u i := closedCoverChart_parameter V Z u c hc i
    calc
      _ = l ≫ ((D.ι i : Z i ⟶ D.glued) ≫ p) := Category.assoc _ _ _
      _ = l ≫ (c i ≫ u i) := congrArg (fun k => l ≫ k) hi
      _ = (l ≫ c i) ≫ u i := (Category.assoc _ _ _).symm
      _ = a ≫ u i := congrArg (fun k => k ≫ u i) hl
      _ = _ := h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.CoverGluing
