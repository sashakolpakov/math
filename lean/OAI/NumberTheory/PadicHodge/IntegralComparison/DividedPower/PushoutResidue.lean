import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Nilpotence

/-! # Pushout Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutResidue

noncomputable section

/-!
# IntegralComparison: the closed subscheme of a divided-power pushout

The closed quotient represents the tensor product of the two original
closed quotients over the common ring. This follows from the actual
pushout universal property by testing against zero divided-power ideals.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Pushout

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (I : Ideal B) (δ : DividedPowers I) (J : Ideal C) (ε : DividedPowers J)

abbrev ideal : Ideal (Pushout.Ring A B C I δ J ε) :=
  (Pushout.envelopeIdeal A B C I δ J).map (Pushout.quotientDP A B C I δ J ε).toRingHom

abbrev Residue := Pushout.Ring A B C I δ J ε ⧸ ideal A B C I δ J ε

def leftResidue : B ⧸ I →+* Residue A B C I δ J ε :=
  Ideal.quotientMap (ideal A B C I δ J ε) (Pushout.leftMap A B C I δ J ε).toRingHom
    (Ideal.map_le_iff_le_comap.mp (Pushout.leftMap A B C I δ J ε).ideal_comp)

def rightResidue : C ⧸ J →+* Residue A B C I δ J ε :=
  Ideal.quotientMap (ideal A B C I δ J ε) (Pushout.rightMap A B C I δ J ε).toRingHom
    (Ideal.map_le_iff_le_comap.mp (Pushout.rightMap A B C I δ J ε).ideal_comp)

def leftBase : A →+* B ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap A B)

def rightBase : A →+* C ⧸ J := (Ideal.Quotient.mk J).comp (algebraMap A C)

lemma residue_agree : (leftResidue A B C I δ J ε).comp (leftBase A B I) =
    (rightResidue A B C I δ J ε).comp (rightBase A C J) := by
  apply RingHom.ext
  intro a
  exact congrArg (Ideal.Quotient.mk (ideal A B C I δ J ε))
    (DFunLike.congr_fun (Pushout.maps_agree A B C I δ J ε) a)

variable {D : Type u} [CommRing D] (b : B ⧸ I →+* D) (c : C ⧸ J →+* D)
variable (h : b.comp (leftBase A B I) = c.comp (rightBase A C J))

def leftToBot : DividedPowers.DPMorphism δ (dividedPowersBot D) :=
  Transfer.mapToBot δ (b.comp (Ideal.Quotient.mk I)) (by
    intro x hx
    change b (Ideal.Quotient.mk I x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero])

def rightToBot : DividedPowers.DPMorphism ε (dividedPowersBot D) :=
  Transfer.mapToBot ε (c.comp (Ideal.Quotient.mk J)) (by
    intro x hx
    change c (Ideal.Quotient.mk J x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero])

def residueLiftDP : DividedPowers.DPMorphism (Pushout.dividedPowers A B C I δ J ε) (dividedPowersBot D) :=
  PushoutLift.lift A B C I δ J ε
    (leftToBot B I δ b) (rightToBot C J ε c) h

def residueLift : Residue A B C I δ J ε →+* D :=
  Ideal.Quotient.lift (ideal A B C I δ J ε) (residueLiftDP A B C I δ J ε b c h).toRingHom
    (Ideal.map_le_iff_le_comap.mp (residueLiftDP A B C I δ J ε b c h).ideal_comp)

lemma residueLift_left : (residueLift A B C I δ J ε b c h).comp (leftResidue A B C I δ J ε) = b := by
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun (PushoutLift.lift_left A B C I δ J ε
    (leftToBot B I δ b) (rightToBot C J ε c) h) y

lemma residueLift_right : (residueLift A B C I δ J ε b c h).comp (rightResidue A B C I δ J ε) = c := by
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun (PushoutLift.lift_right A B C I δ J ε
    (leftToBot B I δ b) (rightToBot C J ε c) h) y

lemma residueLift_unique (m : Residue A B C I δ J ε →+* D)
    (hm : m.comp (leftResidue A B C I δ J ε) = b)
    (hm' : m.comp (rightResidue A B C I δ J ε) = c) : m = residueLift A B C I δ J ε b c h := by
  let ψ := Transfer.mapToBot (Pushout.dividedPowers A B C I δ J ε)
    (m.comp (Ideal.Quotient.mk (ideal A B C I δ J ε))) (by
      intro x hx
      change m (Ideal.Quotient.mk (ideal A B C I δ J ε) x) = 0
      exact (congrArg m (show Ideal.Quotient.mk (ideal A B C I δ J ε) x = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr hx)).trans (map_zero m))
  have he : ψ = residueLiftDP A B C I δ J ε b c h := by
    apply PushoutLift.lift_unique A B C I δ J ε
      (leftToBot B I δ b) (rightToBot C J ε c) h
    · apply DFunLike.ext
      intro x
      exact DFunLike.congr_fun hm (Ideal.Quotient.mk I x)
    · apply DFunLike.ext
      intro x
      exact DFunLike.congr_fun hm' (Ideal.Quotient.mk J x)
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun he y

omit b c h in
lemma ringPushout : IsPushout (CommRingCat.ofHom (leftBase A B I))
    (CommRingCat.ofHom (rightBase A C J)) (CommRingCat.ofHom (leftResidue A B C I δ J ε))
    (CommRingCat.ofHom (rightResidue A B C I δ J ε)) := by
  refine ⟨⟨congrArg CommRingCat.ofHom (residue_agree A B C I δ J ε)⟩, ⟨?_⟩⟩
  apply PushoutCocone.isColimitAux'
  intro s
  let hs := congrArg CommRingCat.Hom.hom s.condition
  refine ⟨CommRingCat.ofHom (residueLift A B C I δ J ε s.inl.hom s.inr.hom hs), ?_, ?_, ?_⟩
  · exact congrArg CommRingCat.ofHom (residueLift_left A B C I δ J ε s.inl.hom s.inr.hom hs)
  · exact congrArg CommRingCat.ofHom (residueLift_right A B C I δ J ε s.inl.hom s.inr.hom hs)
  · intro m hm hm'
    exact congrArg CommRingCat.ofHom (residueLift_unique A B C I δ J ε s.inl.hom s.inr.hom hs
      m.hom (congrArg CommRingCat.Hom.hom hm) (congrArg CommRingCat.Hom.hom hm'))

omit b c h in
lemma schemePullback : IsPullback (Spec.map (CommRingCat.ofHom (rightResidue A B C I δ J ε)))
    (Spec.map (CommRingCat.ofHom (leftResidue A B C I δ J ε)))
    (Spec.map (CommRingCat.ofHom (rightBase A C J))) (Spec.map (CommRingCat.ofHom (leftBase A B I))) :=
  (ringPushout A B C I δ J ε).op.map Scheme.Spec

omit b c h in
lemma prime_nilpotent (p : ℕ) (hp : IsNilpotent (p : B)) : IsNilpotent (p : Pushout.Ring A B C I δ J ε) := by
  simpa only [map_natCast] using hp.map (Pushout.leftMap A B C I δ J ε).toRingHom

omit b c h in
lemma nilIdeal (p : ℕ) (hp : 0 < p) (hpn : IsNilpotent (p : B))
    {x : Pushout.Ring A B C I δ J ε} (hx : x ∈ ideal A B C I δ J ε) : IsNilpotent x :=
  Nilpotence.nilpotent_of_mem (Pushout.dividedPowers A B C I δ J ε) p hp
    (prime_nilpotent A B C I δ J ε p hpn) hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PushoutResidue
