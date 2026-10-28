import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PrescribedPushout
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutExt

/-! # Prescribed Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PrescribedLift

noncomputable section

/-!
# IntegralComparison: the mapping property with a prescribed closed quotient

A compatible pair of divided-power maps extends uniquely when its closed
maps factor through the prescribed quotient. The compatibility is proved
on the two factors and extended by the pushout universal property.
-/

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PrescribedPushout

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (I : Ideal B) (δ : DividedPowers I) (J : Ideal C) (ε : DividedPowers J)
variable (Q : Type u) [CommRing Q]
variable (b : DividedPowers.DPMorphism δ (dividedPowersBot Q))
variable (c : DividedPowers.DPMorphism ε (dividedPowersBot Q))
variable (h : b.toRingHom.comp (algebraMap A B) = c.toRingHom.comp (algebraMap A C))
variable {D : Type u} [CommRing D] {K : Ideal D} {θ : DividedPowers K}
variable (φ : DividedPowers.DPMorphism δ θ) (ψ : DividedPowers.DPMorphism ε θ)
variable (hφ : φ.toRingHom.comp (algebraMap A B) = ψ.toRingHom.comp (algebraMap A C))

def initialLift : DividedPowers.DPMorphism (PrescribedPushout.initialDP A B C I δ J ε) θ :=
  PushoutLift.lift A B C I δ J ε φ ψ hφ

lemma initialLift_left : (initialLift A B C I δ J ε φ ψ hφ).comp (PrescribedPushout.leftInitial A B C I δ J ε) = φ :=
  PushoutLift.lift_left A B C I δ J ε φ ψ hφ

lemma initialLift_right : (initialLift A B C I δ J ε φ ψ hφ).comp (PrescribedPushout.rightInitial A B C I δ J ε) = ψ :=
  PushoutLift.lift_right A B C I δ J ε φ ψ hφ

variable (q : Q →+* D ⧸ K)
variable (hb : q.comp b.toRingHom = (Ideal.Quotient.mk K).comp φ.toRingHom)
variable (hc : q.comp c.toRingHom = (Ideal.Quotient.mk K).comp ψ.toRingHom)

def quotientDP : DividedPowers.DPMorphism θ (dividedPowersBot (D ⧸ K)) :=
  Transfer.mapToBot θ (Ideal.Quotient.mk K)
    (fun _ hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx)

include hb hc in
lemma initialLift_reduction : (Ideal.Quotient.mk K).comp (initialLift A B C I δ J ε φ ψ hφ).toRingHom =
    q.comp (PrescribedPushout.initialReduction A B C I δ J ε Q b c h).toRingHom := by
  have he : (quotientDP (θ := θ)).comp (initialLift A B C I δ J ε φ ψ hφ) =
      (Transfer.botMap q).comp (PrescribedPushout.initialReduction A B C I δ J ε Q b c h) := by
    apply PushoutExt.hom_ext A B C I δ J ε
    · apply DFunLike.ext
      intro x
      exact (congrArg (Ideal.Quotient.mk K) (DFunLike.congr_fun (initialLift_left A B C I δ J ε φ ψ hφ) x)).trans
        ((DFunLike.congr_fun hb x).symm.trans
          (congrArg q (DFunLike.congr_fun (PrescribedPushout.initialReduction_left A B C I δ J ε Q b c h) x)).symm)
    · apply DFunLike.ext
      intro x
      exact (congrArg (Ideal.Quotient.mk K) (DFunLike.congr_fun (initialLift_right A B C I δ J ε φ ψ hφ) x)).trans
        ((DFunLike.congr_fun hc x).symm.trans
          (congrArg q (DFunLike.congr_fun (PrescribedPushout.initialReduction_right A B C I δ J ε Q b c h) x)).symm)
  exact congrArg (fun t : DividedPowers.DPMorphism (PrescribedPushout.initialDP A B C I δ J ε)
    (dividedPowersBot (D ⧸ K)) => t.toRingHom) he

include hb hc in
lemma mapsClosedIdeal : PrescribedPushout.closedIdeal A B C I δ J ε Q b c h ≤
    K.comap (initialLift A B C I δ J ε φ ψ hφ).toRingHom := by
  intro x hx
  change initialLift A B C I δ J ε φ ψ hφ x ∈ K
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have he := DFunLike.congr_fun (initialLift_reduction A B C I δ J ε Q b c h φ ψ hφ q hb hc) x
  exact he.trans ((congrArg q (show PrescribedPushout.initialReduction A B C I δ J ε Q b c h x = 0 from hx)).trans (map_zero q))

def lift : DividedPowers.DPMorphism (PrescribedPushout.dividedPowers A B C I δ J ε Q b c h) θ :=
  Enlargement.lift (PrescribedPushout.Initial A B C I δ J ε)
    (PrescribedPushout.initialIdeal A B C I δ J ε) (PrescribedPushout.initialDP A B C I δ J ε)
    (PrescribedPushout.closedIdeal A B C I δ J ε Q b c h) (initialLift A B C I δ J ε φ ψ hφ)
    (mapsClosedIdeal A B C I δ J ε Q b c h φ ψ hφ q hb hc)

lemma lift_fromInitial : (lift A B C I δ J ε Q b c h φ ψ hφ q hb hc).comp
    (PrescribedPushout.fromInitial A B C I δ J ε Q b c h) = initialLift A B C I δ J ε φ ψ hφ :=
  Enlargement.lift_comp (PrescribedPushout.Initial A B C I δ J ε)
    (PrescribedPushout.initialIdeal A B C I δ J ε) (PrescribedPushout.initialDP A B C I δ J ε)
    (PrescribedPushout.closedIdeal A B C I δ J ε Q b c h) (PrescribedPushout.initialIdeal_le A B C I δ J ε Q b c h)
    (initialLift A B C I δ J ε φ ψ hφ) (mapsClosedIdeal A B C I δ J ε Q b c h φ ψ hφ q hb hc)

lemma lift_left : (lift A B C I δ J ε Q b c h φ ψ hφ q hb hc).comp
    (PrescribedPushout.leftMap A B C I δ J ε Q b c h) = φ := by
  apply DFunLike.ext
  intro x
  exact (DFunLike.congr_fun (lift_fromInitial A B C I δ J ε Q b c h φ ψ hφ q hb hc)
    (PrescribedPushout.leftInitial A B C I δ J ε x)).trans (DFunLike.congr_fun (initialLift_left A B C I δ J ε φ ψ hφ) x)

lemma lift_right : (lift A B C I δ J ε Q b c h φ ψ hφ q hb hc).comp
    (PrescribedPushout.rightMap A B C I δ J ε Q b c h) = ψ := by
  apply DFunLike.ext
  intro x
  exact (DFunLike.congr_fun (lift_fromInitial A B C I δ J ε Q b c h φ ψ hφ q hb hc)
    (PrescribedPushout.rightInitial A B C I δ J ε x)).trans (DFunLike.congr_fun (initialLift_right A B C I δ J ε φ ψ hφ) x)

lemma lift_unique (g : DividedPowers.DPMorphism (PrescribedPushout.dividedPowers A B C I δ J ε Q b c h) θ)
    (hgB : g.comp (PrescribedPushout.leftMap A B C I δ J ε Q b c h) = φ)
    (hgC : g.comp (PrescribedPushout.rightMap A B C I δ J ε Q b c h) = ψ) :
    g = lift A B C I δ J ε Q b c h φ ψ hφ q hb hc := by
  have he : g.comp (PrescribedPushout.fromInitial A B C I δ J ε Q b c h) = initialLift A B C I δ J ε φ ψ hφ := by
    apply PushoutExt.hom_ext A B C I δ J ε
    · exact hgB.trans (initialLift_left A B C I δ J ε φ ψ hφ).symm
    · exact hgC.trans (initialLift_right A B C I δ J ε φ ψ hφ).symm
  exact Enlargement.lift_unique (PrescribedPushout.Initial A B C I δ J ε)
    (PrescribedPushout.initialIdeal A B C I δ J ε) (PrescribedPushout.initialDP A B C I δ J ε)
    (PrescribedPushout.closedIdeal A B C I δ J ε Q b c h) (PrescribedPushout.initialIdeal_le A B C I δ J ε Q b c h)
    (initialLift A B C I δ J ε φ ψ hφ) (mapsClosedIdeal A B C I δ J ε Q b c h φ ψ hφ q hb hc) g he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PrescribedLift
