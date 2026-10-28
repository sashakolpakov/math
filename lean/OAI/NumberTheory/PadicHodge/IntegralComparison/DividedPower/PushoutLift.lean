import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Pushout

/-! # Pushout Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutLift

noncomputable section

/-!
# IntegralComparison: the universal property of the divided-power pushout

Every compatible pair of divided-power maps factors uniquely through
the constructed tensor-envelope quotient.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Pushout

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (I : Ideal B) (δ : DividedPowers I) (J : Ideal C) (ε : DividedPowers J)
variable {D : Type u} [CommRing D] {K : Ideal D} {θ : DividedPowers K}
variable (b : DividedPowers.DPMorphism δ θ) (c : DividedPowers.DPMorphism ε θ)
variable (h : b.toRingHom.comp (algebraMap A B) = c.toRingHom.comp (algebraMap A C))

def tensorMap : Pushout.Tensor A B C →+* D :=
  ((CommRingCat.isPushout_tensorProduct A B C).desc (CommRingCat.ofHom b.toRingHom)
    (CommRingCat.ofHom c.toRingHom) (congrArg CommRingCat.ofHom h)).hom

lemma tensorMap_left : (tensorMap A B C I δ J ε b c h).comp (Pushout.leftRingMap A B C) = b.toRingHom :=
  congrArg CommRingCat.Hom.hom ((CommRingCat.isPushout_tensorProduct A B C).inl_desc
    (CommRingCat.ofHom b.toRingHom) (CommRingCat.ofHom c.toRingHom) (congrArg CommRingCat.ofHom h))

lemma tensorMap_right : (tensorMap A B C I δ J ε b c h).comp (Pushout.rightRingMap A B C) = c.toRingHom :=
  congrArg CommRingCat.Hom.hom ((CommRingCat.isPushout_tensorProduct A B C).inr_desc
    (CommRingCat.ofHom b.toRingHom) (CommRingCat.ofHom c.toRingHom) (congrArg CommRingCat.ofHom h))

def target : PowerEnvelope.Target B (Pushout.Tensor A B C) I δ
    (Pushout.leftRingMap A B C) (Pushout.tensorIdeal A B C I J) where
  ring := D
  ideal := K
  dividedPowers := θ
  fromBase := tensorMap A B C I δ J ε b c h
  mapsIdeal := by
    apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      change tensorMap A B C I δ J ε b c h (Pushout.leftRingMap A B C x) ∈ K
      rw [show tensorMap A B C I δ J ε b c h (Pushout.leftRingMap A B C x) = b x from
        DFunLike.congr_fun (tensorMap_left A B C I δ J ε b c h) x]
      exact b.ideal_comp (Ideal.mem_map_of_mem _ hx)
    · apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      change tensorMap A B C I δ J ε b c h (Pushout.rightRingMap A B C x) ∈ K
      rw [show tensorMap A B C I δ J ε b c h (Pushout.rightRingMap A B C x) = c x from
        DFunLike.congr_fun (tensorMap_right A B C I δ J ε b c h) x]
      exact c.ideal_comp (Ideal.mem_map_of_mem _ hx)
  baseCompatible := by rw [tensorMap_left]; exact b.isDPMorphism

def envelopeLift : DividedPowers.DPMorphism (Pushout.envelopeDividedPowers A B C I δ J) θ :=
  PowerEnvelope.lift B (Pushout.Tensor A B C) I δ (Pushout.leftRingMap A B C)
    (Pushout.tensorIdeal A B C I J) (target A B C I δ J ε b c h)

lemma envelopeLift_tensor : (envelopeLift A B C I δ J ε b c h).toRingHom.comp (Pushout.toEnvelope A B C I δ J) =
    tensorMap A B C I δ J ε b c h :=
  PowerEnvelope.lift_fromBase B (Pushout.Tensor A B C) I δ (Pushout.leftRingMap A B C)
    (Pushout.tensorIdeal A B C I J) (target A B C I δ J ε b c h)

lemma envelopeLift_left : (envelopeLift A B C I δ J ε b c h).comp (Pushout.leftToEnvelope A B C I δ J) = b := by
  apply DFunLike.ext
  intro x
  have ht := DFunLike.congr_fun (envelopeLift_tensor A B C I δ J ε b c h) (Pushout.leftRingMap A B C x)
  exact ht.trans (DFunLike.congr_fun (tensorMap_left A B C I δ J ε b c h) x)

lemma envelopeLift_right : (envelopeLift A B C I δ J ε b c h).toRingHom.comp (Pushout.rightToEnvelope A B C I δ J) =
    c.toRingHom := by
  change ((envelopeLift A B C I δ J ε b c h).toRingHom.comp (Pushout.toEnvelope A B C I δ J)).comp (Pushout.rightRingMap A B C) = _
  rw [envelopeLift_tensor, tensorMap_right]

lemma kills_relations : ∀ x ∈ Pushout.relations A B C I δ J ε, envelopeLift A B C I δ J ε b c h x = 0 := by
  rintro _ ⟨n, _hn, x, hx, rfl⟩
  change (envelopeLift A B C I δ J ε b c h).toRingHom (_ - _) = 0
  rw [map_sub, ← (envelopeLift A B C I δ J ε b c h).dpow_comp _ (Pushout.right_ideal A B C I δ J hx)]
  have h₁ := DFunLike.congr_fun (envelopeLift_right A B C I δ J ε b c h) x
  have h₂ := DFunLike.congr_fun (envelopeLift_right A B C I δ J ε b c h) (ε.dpow n x)
  change θ.dpow n ((envelopeLift A B C I δ J ε b c h).toRingHom (Pushout.rightToEnvelope A B C I δ J x)) -
    (envelopeLift A B C I δ J ε b c h).toRingHom (Pushout.rightToEnvelope A B C I δ J (ε.dpow n x)) = 0
  simp only [RingHom.comp_apply] at h₁ h₂
  rw [h₁, h₂]
  exact sub_eq_zero.mpr (c.dpow_comp x hx)

def lift : DividedPowers.DPMorphism (Pushout.dividedPowers A B C I δ J ε) θ :=
  Relations.lift (Pushout.envelopeDividedPowers A B C I δ J)
    (Pushout.relations A B C I δ J ε) (Pushout.relations_subset A B C I δ J ε)
    (envelopeLift A B C I δ J ε b c h) (kills_relations A B C I δ J ε b c h)

lemma lift_left : (lift A B C I δ J ε b c h).comp (Pushout.leftMap A B C I δ J ε) = b := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (envelopeLift_left A B C I δ J ε b c h) x

lemma lift_right : (lift A B C I δ J ε b c h).comp (Pushout.rightMap A B C I δ J ε) = c := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (envelopeLift_right A B C I δ J ε b c h) x

lemma lift_unique (ψ : DividedPowers.DPMorphism (Pushout.dividedPowers A B C I δ J ε) θ)
    (hleft : ψ.comp (Pushout.leftMap A B C I δ J ε) = b) (hright : ψ.comp (Pushout.rightMap A B C I δ J ε) = c) :
    ψ = lift A B C I δ J ε b c h := by
  have he : ψ.comp (Pushout.quotientDP A B C I δ J ε) = envelopeLift A B C I δ J ε b c h := by
    apply PowerEnvelope.lift_unique B (Pushout.Tensor A B C) I δ (Pushout.leftRingMap A B C)
      (Pushout.tensorIdeal A B C I J) (target A B C I δ J ε b c h)
    have ht : CommRingCat.ofHom
        (((ψ.comp (Pushout.quotientDP A B C I δ J ε)).toRingHom).comp (Pushout.toEnvelope A B C I δ J)) =
        CommRingCat.ofHom (tensorMap A B C I δ J ε b c h) := by
      apply (CommRingCat.isPushout_tensorProduct A B C).hom_ext
      · change CommRingCat.ofHom ((ψ.comp (Pushout.leftMap A B C I δ J ε)).toRingHom) =
          CommRingCat.ofHom ((tensorMap A B C I δ J ε b c h).comp (Pushout.leftRingMap A B C))
        rw [hleft, tensorMap_left]
      · change CommRingCat.ofHom ((ψ.comp (Pushout.rightMap A B C I δ J ε)).toRingHom) =
          CommRingCat.ofHom ((tensorMap A B C I δ J ε b c h).comp (Pushout.rightRingMap A B C))
        rw [hright, tensorMap_right]
    exact congrArg CommRingCat.Hom.hom ht
  exact Relations.lift_unique (Pushout.envelopeDividedPowers A B C I δ J)
    (Pushout.relations A B C I δ J ε) (Pushout.relations_subset A B C I δ J ε)
    (envelopeLift A B C I δ J ε b c h) (kills_relations A B C I δ J ε b c h) ψ he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutLift
