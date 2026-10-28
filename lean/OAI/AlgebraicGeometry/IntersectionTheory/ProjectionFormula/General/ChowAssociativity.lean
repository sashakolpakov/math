import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.TripleMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowSymmetry

/-! # Chow Associativity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowAssociativity

noncomputable section

/-! The native Chow intersection is commutative and associative in
all codimensions. Triple moving and the actual iterated Tor Euler
identity prove associativity without additional geometric hypotheses. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem chow_trans (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {p q t : ℕ} (h : p = q) (h' : q = t)
    (a : ProperCycleLinearity.ChowQ X p) :
    DegreeCast.chow X h' (DegreeCast.chow X h a) = DegreeCast.chow X (h.trans h') a := by
  subst q
  subst t
  rfl

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]

theorem mk_proper (p q : ℕ) (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) :
    GeneralChowIntersection.chowMap X m p q (ProperCycleLinearity.cycleToChowQ X p a) (ProperCycleLinearity.cycleToChowQ X q b) =
      ProperCycleLinearity.cycleToChowQ X (p + q) (Supports.ProperCycle.intersectionBilinear X m p q a b) :=
  GeneralChowIntersection.Value.value_of_proper X m p q a b hp

theorem comm (p q : ℕ) (a : ProperCycleLinearity.ChowQ X p) (b : ProperCycleLinearity.ChowQ X q) :
    DegreeCast.chow X (Nat.add_comm p q) (GeneralChowIntersection.chowMap X m p q a b) = GeneralChowIntersection.chowMap X m q p b a := by
  have h : GeneralChowIntersection.chowMap X m p q a b ∈ ProperCycleLinearity.chowIntersection X p q a b := by
    rw [GeneralChowIntersection.chowIntersection_eq_singleton X m p q]
    exact Set.mem_singleton _
  have he := (ChowSymmetry.mem_comm X p q a b _).mp h
  rwa [GeneralChowIntersection.chowIntersection_eq_singleton X m q p, Set.mem_singleton_iff] at he

theorem cast_left {p r : ℕ} (h : p = r) (q : ℕ) (a : ProperCycleLinearity.ChowQ X p) (b : ProperCycleLinearity.ChowQ X q) :
    DegreeCast.chow X (congrArg (fun k => k + q) h) (GeneralChowIntersection.chowMap X m p q a b) =
      GeneralChowIntersection.chowMap X m r q (DegreeCast.chow X h a) b := by
  subst r
  rfl

theorem swap (p q t : ℕ) (α : ProperCycleLinearity.ChowQ X p) (β : ProperCycleLinearity.ChowQ X q) (γ : ProperCycleLinearity.ChowQ X t) :
    DegreeCast.chow X (show p + q + t = p + t + q by omega)
      (GeneralChowIntersection.chowMap X m (p + q) t (GeneralChowIntersection.chowMap X m p q α β) γ) =
      GeneralChowIntersection.chowMap X m (p + t) q (GeneralChowIntersection.chowMap X m p t α γ) β := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p α
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q β
  obtain ⟨c, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X t γ
  obtain ⟨a', b', ha, hb, hab, hac, _, ht⟩ :=
    TripleMoving.representatives X m p q t a b c
  rw [(ProperCycleLinearity.cycleToChowQ_eq_iff X p a a').mpr ha, (ProperCycleLinearity.cycleToChowQ_eq_iff X q b b').mpr hb,
    mk_proper X m p q a' b' hab, mk_proper X m p t a' c hac,
    mk_proper X m (p + q) t _ c (Proper.TripleCycles.proper X m p q t a' b' c hab ht),
    mk_proper X m (p + t) q _ b' (Proper.TripleCycles.proper X m p t q a' c b' hac
      (Proper.TripleCycles.meetTriply_swap X p q t a' b' c ht)), DegreeCast.chow_mk,
    Proper.TripleCycles.swap X m p q t a' b' c hab hac ht]

theorem assoc (p q t : ℕ) (α : ProperCycleLinearity.ChowQ X p) (β : ProperCycleLinearity.ChowQ X q) (γ : ProperCycleLinearity.ChowQ X t) :
    DegreeCast.chow X (Nat.add_assoc p q t)
      (GeneralChowIntersection.chowMap X m (p + q) t (GeneralChowIntersection.chowMap X m p q α β) γ) =
      GeneralChowIntersection.chowMap X m p (q + t) α (GeneralChowIntersection.chowMap X m q t β γ) := by
  let h₁ : p + q + t = q + p + t := congrArg (fun k => k + t) (Nat.add_comm p q)
  let h₂ : q + p + t = q + t + p := by omega
  let h₃ : q + t + p = p + (q + t) := Nat.add_comm (q + t) p
  calc
    _ = DegreeCast.chow X h₃ (DegreeCast.chow X h₂ (DegreeCast.chow X h₁
        (GeneralChowIntersection.chowMap X m (p + q) t (GeneralChowIntersection.chowMap X m p q α β) γ))) := by rw [chow_trans, chow_trans]
    _ = DegreeCast.chow X h₃
        (GeneralChowIntersection.chowMap X m (q + t) p (GeneralChowIntersection.chowMap X m q t β γ) α) := by
      rw [cast_left X m (Nat.add_comm p q) t, comm X m p q, swap X m q p t]
    _ = _ := comm X m (q + t) p _ α

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowAssociativity
