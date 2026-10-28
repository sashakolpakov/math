import OAI.ArithmeticGeometry.Models.SpreadingOut.Graph

/-! # Dense Chart Factor -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.DenseChartFactor.Construction

noncomputable section

/-! Extension of closed affine-chart conditions from a dense subscheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem reduced_factors_through_closed_of_dominant
    {W X Y T : Scheme.{u}} (d : W ⟶ X) [IsDominant d] [IsReduced X]
    (f : X ⟶ T) (i : Y ⟶ T) [IsClosedImmersion i]
    (k : W ⟶ Y) (h : d ≫ f = k ≫ i) :
    ∃ l : X ⟶ Y, l ≫ i = f := by
  let a := pullback.lift k d h.symm
  have : IsDominant (a ≫ pullback.snd i f) := by
    rw [pullback.lift_snd]
    infer_instance
  have : IsDominant (pullback.snd i f) := IsDominant.of_comp a (pullback.snd i f)
  have : Surjective (pullback.snd i f) := inferInstance
  have : IsIso (pullback.snd i f) :=
    isIso_of_isClosedImmersion_of_surjective (pullback.snd i f)
  refine ⟨inv (pullback.snd i f) ≫ pullback.fst i f, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- If a dense part of a reduced scheme lies in a closed affine chart,
its two coordinate maps factor through that chart everywhere. -/
theorem factor_through_chart_of_dense
    {S : Scheme.{u}} {W Z U X A : Over S}
    [IsSeparated X.hom] [IsReduced Z.left]
    (d : W ⟶ Z) [IsDominant d.left]
    (j : U ⟶ X) (e : U ⟶ A) [IsClosedImmersion e.left]
    (p : Z ⟶ X) (q : Z ⟶ A) (k : W ⟶ U)
    (hp : d.left ≫ p.left = k.left ≫ j.left)
    (hq : d.left ≫ q.left = k.left ≫ e.left) :
    ∃ l : Z ⟶ U, l.left ≫ j.left = p.left ∧ l.left ≫ e.left = q.left := by
  let i := pullback.lift j.left e.left (j.w.trans e.w.symm)
  have : IsClosedImmersion i :=
    Graph.Construction.pullback_lift_closedImmersion_of_right X.hom A.hom j.left e.left _
  let f := pullback.lift p.left q.left (p.w.trans q.w.symm)
  have h : d.left ≫ f = k.left ≫ i := by
    apply pullback.hom_ext
    · simpa only [f, i, Category.assoc, pullback.lift_fst] using hp
    · simpa only [f, i, Category.assoc, pullback.lift_snd] using hq
  obtain ⟨l, hl⟩ := reduced_factors_through_closed_of_dominant d.left f i k.left h
  have hlj : l ≫ j.left = p.left := by
    have h := congrArg (fun a ↦ a ≫ pullback.fst X.hom A.hom) hl
    simpa only [f, i, Category.assoc, pullback.lift_fst] using h
  have hle : l ≫ e.left = q.left := by
    have h := congrArg (fun a ↦ a ≫ pullback.snd X.hom A.hom) hl
    simpa only [f, i, Category.assoc, pullback.lift_snd] using h
  refine ⟨Over.homMk l ?_, hlj, hle⟩
  rw [← e.w, ← Category.assoc, hle, q.w]

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.DenseChartFactor.Construction
