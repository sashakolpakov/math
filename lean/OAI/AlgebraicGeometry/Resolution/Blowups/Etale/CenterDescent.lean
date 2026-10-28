import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.FlatIdealDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalContainmentNeighborhood
import Mathlib.RingTheory.RingHom.Etale

/-! # Center Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CenterDescent.Construction

noncomputable section

/-! Descent of center equality from pointed flat and étale comparisons. -/

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The local descent statement for a raw flat ring map. -/
theorem flat_map_ideal_equality_at_prime (f : R →+* S) (hf : f.Flat)
    (J K q : Ideal R) [q.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hQ : Q.comap f = q) (h : J.map f = K.map f) :
    J.map (algebraMap R (Localization.AtPrime q)) =
      K.map (algebraMap R (Localization.AtPrime q)) := by
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hf
  have hlocal := Pointed.FlatIdealDescent.Construction.flat_ideal_equality_reflects_at_prime J K Q h
  have hunder : Q.under R = q := hQ
  subst q
  exact hlocal

/-- Equality of finite center ideals on a pointed flat chart holds on an
actual principal open neighborhood of its image point. -/
theorem flat_map_ideal_equality_neighborhood (f : R →+* S) (hf : f.Flat)
    (J K q : Ideal R) [q.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hQ : Q.comap f = q) (hJ : J.FG) (hK : K.FG)
    (h : J.map f = K.map f) :
    ∃ s ∉ q, J.map (algebraMap R (Localization.Away s)) =
      K.map (algebraMap R (Localization.Away s)) :=
  LocalContainmentNeighborhood.Construction.exists_neighborhood_ideal_equality J K q hJ hK
    (flat_map_ideal_equality_at_prime f hf J K q Q hQ h)

variable {k C : Type*} [CommRing k] [Field C]
  [Algebra k R] [Algebra k S] [Algebra k C]

/-- The two center constructions may use different étale comparison maps.
Once the second center is preserved by the comparison, equality on the
common chart descends to an open neighborhood of the original point. -/
theorem pointed_etale_center_equality_neighborhood
    (f g : R →ₐ[k] S) (hf : f.toRingHom.Etale)
    (v : S →ₐ[k] C) (r : R →ₐ[k] C) (hv : ∀ x : R, v (f x) = r x)
    (I L : Ideal R) (hI : I.FG) (hL : L.FG)
    (hcompare : I.map f.toRingHom = L.map g.toRingHom)
    (hpreserve : L.map f.toRingHom = L.map g.toRingHom) :
    ∃ s : R, r s ≠ 0 ∧ I.map (algebraMap R (Localization.Away s)) =
      L.map (algebraMap R (Localization.Away s)) := by
  let q := RingHom.ker r.toRingHom
  let Q := RingHom.ker v.toRingHom
  let : q.IsPrime := Ideal.comap_isPrime r.toRingHom ⊥
  let : Q.IsPrime := Ideal.comap_isPrime v.toRingHom ⊥
  have hQ : Q.comap f.toRingHom = q := by
    ext x
    change v (f x) = 0 ↔ r x = 0
    rw [hv x]
  have hflat := (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1
  obtain ⟨s, hs, heq⟩ := flat_map_ideal_equality_neighborhood f.toRingHom hflat
    I L q Q hQ hI hL (hcompare.trans hpreserve.symm)
  exact ⟨s, hs, heq⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CenterDescent.Construction
