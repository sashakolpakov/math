import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Enlargement

/-! # Prescribed Pushout -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PrescribedPushout

noncomputable section

/-!
# IntegralComparison: divided-power pushouts with a prescribed closed quotient

After forming the divided-power pushout, enlarge its divided-power ideal
to the kernel of a prescribed closed quotient. The resulting envelope
has that quotient as its actual closed subscheme when the quotient map
is surjective.
-/

universe u

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (I : Ideal B) (δ : DividedPowers I) (J : Ideal C) (ε : DividedPowers J)
variable (Q : Type u) [CommRing Q]
variable (b : DividedPowers.DPMorphism δ (dividedPowersBot Q))
variable (c : DividedPowers.DPMorphism ε (dividedPowersBot Q))
variable (h : b.toRingHom.comp (algebraMap A B) = c.toRingHom.comp (algebraMap A C))

def Initial := Pushout.Ring A B C I δ J ε

instance initialCommRing : CommRing (Initial A B C I δ J ε) :=
  inferInstanceAs (CommRing (Pushout.Ring A B C I δ J ε))

abbrev initialIdeal : Ideal (Initial A B C I δ J ε) := PushoutResidue.ideal A B C I δ J ε

def initialDP : DividedPowers (initialIdeal A B C I δ J ε) := Pushout.dividedPowers A B C I δ J ε

def leftInitial : DividedPowers.DPMorphism δ (initialDP A B C I δ J ε) :=
  Pushout.leftMap A B C I δ J ε

def rightInitial : DividedPowers.DPMorphism ε (initialDP A B C I δ J ε) :=
  Pushout.rightMap A B C I δ J ε

def initialReduction : DividedPowers.DPMorphism (initialDP A B C I δ J ε) (dividedPowersBot Q) :=
  PushoutLift.lift A B C I δ J ε b c h

lemma initialReduction_left : (initialReduction A B C I δ J ε Q b c h).comp
    (leftInitial A B C I δ J ε) = b :=
  PushoutLift.lift_left A B C I δ J ε b c h

lemma initialReduction_right : (initialReduction A B C I δ J ε Q b c h).comp
    (rightInitial A B C I δ J ε) = c :=
  PushoutLift.lift_right A B C I δ J ε b c h

abbrev closedIdeal := RingHom.ker (initialReduction A B C I δ J ε Q b c h).toRingHom

lemma initialIdeal_le : initialIdeal A B C I δ J ε ≤ closedIdeal A B C I δ J ε Q b c h :=
  Ideal.map_le_iff_le_comap.mp (initialReduction A B C I δ J ε Q b c h).ideal_comp

abbrev Ring := Enlargement.Ring (Initial A B C I δ J ε)
  (initialIdeal A B C I δ J ε) (initialDP A B C I δ J ε) (closedIdeal A B C I δ J ε Q b c h)

abbrev ideal := Enlargement.ideal (Initial A B C I δ J ε)
  (initialIdeal A B C I δ J ε) (initialDP A B C I δ J ε) (closedIdeal A B C I δ J ε Q b c h)

abbrev dividedPowers := Enlargement.dividedPowers (Initial A B C I δ J ε)
  (initialIdeal A B C I δ J ε) (initialDP A B C I δ J ε) (closedIdeal A B C I δ J ε Q b c h)

def fromInitial : DividedPowers.DPMorphism (initialDP A B C I δ J ε)
    (dividedPowers A B C I δ J ε Q b c h) :=
  Enlargement.map (Initial A B C I δ J ε)
    (initialIdeal A B C I δ J ε) (initialDP A B C I δ J ε)
    (closedIdeal A B C I δ J ε Q b c h) (initialIdeal_le A B C I δ J ε Q b c h)

def leftMap : DividedPowers.DPMorphism δ (dividedPowers A B C I δ J ε Q b c h) :=
  (fromInitial A B C I δ J ε Q b c h).comp (leftInitial A B C I δ J ε)

def rightMap : DividedPowers.DPMorphism ε (dividedPowers A B C I δ J ε Q b c h) :=
  (fromInitial A B C I δ J ε Q b c h).comp (rightInitial A B C I δ J ε)

lemma maps_agree : (leftMap A B C I δ J ε Q b c h).toRingHom.comp (algebraMap A B) =
    (rightMap A B C I δ J ε Q b c h).toRingHom.comp (algebraMap A C) := by
  apply RingHom.ext
  intro a
  exact congrArg (fromInitial A B C I δ J ε Q b c h)
    (DFunLike.congr_fun (Pushout.maps_agree A B C I δ J ε) a)

variable (hq : Function.Surjective (initialReduction A B C I δ J ε Q b c h))

def residueEquiv : Ring A B C I δ J ε Q b c h ⧸ ideal A B C I δ J ε Q b c h ≃+* Q :=
  (Enlargement.residueEquiv (Initial A B C I δ J ε)
    (initialIdeal A B C I δ J ε) (initialDP A B C I δ J ε)
    (closedIdeal A B C I δ J ε Q b c h) (initialIdeal_le A B C I δ J ε Q b c h)).symm.trans
    (RingHom.quotientKerEquivOfSurjective hq)

lemma residueEquiv_mk (x : Initial A B C I δ J ε) :
    residueEquiv A B C I δ J ε Q b c h hq
      (Ideal.Quotient.mk (ideal A B C I δ J ε Q b c h) (fromInitial A B C I δ J ε Q b c h x)) =
    initialReduction A B C I δ J ε Q b c h x := by
  let e := Enlargement.residueEquiv (Initial A B C I δ J ε)
    (initialIdeal A B C I δ J ε) (initialDP A B C I δ J ε)
    (closedIdeal A B C I δ J ε Q b c h) (initialIdeal_le A B C I δ J ε Q b c h)
  have he : e (Ideal.Quotient.mk (closedIdeal A B C I δ J ε Q b c h) x) =
      Ideal.Quotient.mk (ideal A B C I δ J ε Q b c h) (fromInitial A B C I δ J ε Q b c h x) := rfl
  have hs := (congrArg e.symm he).symm.trans (e.symm_apply_apply _)
  exact (congrArg (RingHom.quotientKerEquivOfSurjective hq) hs).trans rfl

lemma residueEquiv_left (x : B) : residueEquiv A B C I δ J ε Q b c h hq
    (Ideal.Quotient.mk (ideal A B C I δ J ε Q b c h) (leftMap A B C I δ J ε Q b c h x)) = b x := by
  exact (residueEquiv_mk A B C I δ J ε Q b c h hq
    (Pushout.leftMap A B C I δ J ε x)).trans
    (DFunLike.congr_fun (PushoutLift.lift_left A B C I δ J ε b c h) x)

lemma residueEquiv_right (x : C) : residueEquiv A B C I δ J ε Q b c h hq
    (Ideal.Quotient.mk (ideal A B C I δ J ε Q b c h) (rightMap A B C I δ J ε Q b c h x)) = c x := by
  exact (residueEquiv_mk A B C I δ J ε Q b c h hq
    (Pushout.rightMap A B C I δ J ε x)).trans
    (DFunLike.congr_fun (PushoutLift.lift_right A B C I δ J ε b c h) x)

omit hq in
lemma prime_nilpotent (p : ℕ) (hp : IsNilpotent (p : B)) : IsNilpotent (p : Ring A B C I δ J ε Q b c h) := by
  simpa only [map_natCast] using hp.map (leftMap A B C I δ J ε Q b c h).toRingHom

omit hq in
lemma nilIdeal (p : ℕ) (hp : 0 < p) (hpn : IsNilpotent (p : B))
    {x : Ring A B C I δ J ε Q b c h} (hx : x ∈ ideal A B C I δ J ε Q b c h) : IsNilpotent x :=
  Nilpotence.nilpotent_of_mem (dividedPowers A B C I δ J ε Q b c h) p hp
    (prime_nilpotent A B C I δ J ε Q b c h p hpn) hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PrescribedPushout
