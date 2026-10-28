import OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedImmersionDescent

/-! # Restricted Graph -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.RestrictedGraph.Construction

noncomputable section

/-! Restricting a closed relative graph along an open subset of its second
factor preserves the closed graph embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem restricted_graph_closedImmersion
    {S : Scheme.{u}} {Z X P : Over S}
    (p : Z ⟶ X) (q : Z ⟶ P)
    [IsClosedImmersion (pullback.lift p.left q.left (p.w.trans q.w.symm))]
    (V : P.left.Opens)
    (h : ((q.left ⁻¹ᵁ V).ι ≫ p.left) ≫ X.hom = (q.left ∣_ V) ≫ (V.ι ≫ P.hom)) :
    IsClosedImmersion
      (pullback.lift ((q.left ⁻¹ᵁ V).ι ≫ p.left) (q.left ∣_ V) h) := by
  let i := pullback.lift p.left q.left (p.w.trans q.w.symm)
  let A : Over P.left := Over.mk q.left
  let B : Over P.left := Over.mk (pullback.snd X.hom P.hom)
  let a : A ⟶ B := Over.homMk i (pullback.lift_snd _ _ _)
  have : IsClosedImmersion a.left :=
    inferInstanceAs (IsClosedImmersion (pullback.lift p.left q.left (p.w.trans q.w.symm)))
  let F := Over.pullback V.ι
  have : IsClosedImmersion (F.map a).left := ClosedImmersionDescent.Construction.baseChange_closedImmersion V.ι a
  let e := (isPullback_morphismRestrict q.left V).flip.isoPullback
  let v := pullbackLeftPullbackSndIso X.hom P.hom V.ι
  let l := e.hom ≫ (F.map a).left ≫ v.hom
  have he₁ : e.hom ≫ pullback.fst q.left V.ι = (q.left ⁻¹ᵁ V).ι :=
    (isPullback_morphismRestrict q.left V).flip.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd q.left V.ι = q.left ∣_ V :=
    (isPullback_morphismRestrict q.left V).flip.isoPullback_hom_snd
  have ha₁ : (F.map a).left ≫ pullback.fst (pullback.snd X.hom P.hom) V.ι =
      pullback.fst q.left V.ι ≫ i :=
    (FoundationsPullback.Constructions.pullback_over_map_isPullback V.ι a).w
  have ha₂ : (F.map a).left ≫ pullback.snd (pullback.snd X.hom P.hom) V.ι =
      pullback.snd q.left V.ι := (F.map a).w
  have hi : i ≫ pullback.fst X.hom P.hom = p.left := pullback.lift_fst _ _ _
  have hl : l = pullback.lift ((q.left ⁻¹ᵁ V).ι ≫ p.left) (q.left ∣_ V) h := by
    apply pullback.hom_ext
    · simp only [l, v, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
        reassoc_of% ha₁, hi, reassoc_of% he₁, pullback.lift_fst]
    · simp only [l, v, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
        ha₂, he₂, pullback.lift_snd]
  rw [← hl]
  exact inferInstanceAs (IsClosedImmersion (e.hom ≫ (F.map a).left ≫ v.hom))

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.RestrictedGraph.Construction
