import OAI.AlgebraicGeometry.Picard.Homomorphisms.PolynomialRank
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.PolynomialAlgebra

/-! # Finite Free Rank -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteFreeRank

noncomputable section

/-! Explicit finite-free ranks for ring maps, including composition and polynomial base change. -/

open _root_.Module _root_.Polynomial

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]

def RingHomHasFiniteBasis (f : R →+* S) (n : ℕ) : Prop :=
  letI := f.toAlgebra
  Nonempty (Basis (Fin n) R S)

theorem ringHomHasFiniteBasis_algebraMap [Algebra R S] (n : ℕ) :
    RingHomHasFiniteBasis (algebraMap R S) n ↔ Nonempty (Basis (Fin n) R S) := by
  unfold RingHomHasFiniteBasis
  rw [toAlgebra_algebraMap]

theorem ringHomHasFiniteBasis_of_bijective (f : R →+* S) (hf : Function.Bijective f) :
    RingHomHasFiniteBasis f 1 := by
  algebraize [f]
  apply (ringHomHasFiniteBasis_algebraMap 1).mpr
  exact ⟨(Basis.singleton (Fin 1) R).map (LinearEquiv.ofBijective (Algebra.linearMap R S) hf)⟩

theorem RingHomHasFiniteBasis.comp {f : R →+* S} {g : S →+* T} {m n : ℕ}
    (hf : RingHomHasFiniteBasis f m) (hg : RingHomHasFiniteBasis g n) :
    RingHomHasFiniteBasis (g.comp f) (m * n) := by
  algebraize [f, g, g.comp f]
  obtain ⟨b⟩ := (ringHomHasFiniteBasis_algebraMap m).mp hf
  obtain ⟨c⟩ := (ringHomHasFiniteBasis_algebraMap n).mp hg
  apply (ringHomHasFiniteBasis_algebraMap (m * n)).mpr
  exact ⟨(b.smulTower c).reindex finProdFinEquiv⟩

theorem RingHomHasFiniteBasis.polynomial {f : R →+* S} {n : ℕ}
    (hf : RingHomHasFiniteBasis f n) : RingHomHasFiniteBasis (Polynomial.mapRingHom f) n := by
  algebraize [f]
  obtain ⟨b⟩ := (ringHomHasFiniteBasis_algebraMap n).mp hf
  let : Algebra R[X] S[X] := Polynomial.algebra R S
  change RingHomHasFiniteBasis (algebraMap R[X] S[X]) n
  apply (ringHomHasFiniteBasis_algebraMap n).mpr
  exact ⟨(b.baseChange R[X]).map (Algebra.IsPushout.equiv R R[X] S S[X]).toLinearEquiv⟩

theorem RingHomHasFiniteBasis.finite {f : R →+* S} {n : ℕ}
    (hf : RingHomHasFiniteBasis f n) : f.Finite := by
  algebraize [f]
  obtain ⟨b⟩ := (ringHomHasFiniteBasis_algebraMap n).mp hf
  exact RingHom.finite_algebraMap.mpr (Module.Finite.of_basis b)

theorem RingHomHasFiniteBasis.flat {f : R →+* S} {n : ℕ}
    (hf : RingHomHasFiniteBasis f n) : f.Flat := by
  algebraize [f]
  obtain ⟨b⟩ := (ringHomHasFiniteBasis_algebraMap n).mp hf
  have : Module.Free R S := Module.Free.of_basis b
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem RingHomHasFiniteBasis.finrank {f : R →+* S} {n : ℕ} [Nontrivial R]
    (hf : RingHomHasFiniteBasis f n) (x : PrimeSpectrum R) : f.finrank x = n := by
  algebraize [f]
  obtain ⟨b⟩ := (ringHomHasFiniteBasis_algebraMap n).mp hf
  have : Module.Free R S := Module.Free.of_basis b
  change (algebraMap R S).finrank x = n
  rw [RingHom.finrank_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  simpa using Module.finrank_eq_card_basis b

theorem polynomial_expand_hasFiniteBasis (R : Type u) [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) : RingHomHasFiniteBasis (expand R n).toRingHom n := by
  have ho : RingHomHasFiniteBasis (AdjoinRoot.of (Homomorphisms.Polynomial.Construction.expansionPolynomial R n)) n :=
    (ringHomHasFiniteBasis_algebraMap n).mpr ⟨PolynomialRank.Construction.polynomialExpansionRootBasis R n hn⟩
  have hl := ringHomHasFiniteBasis_of_bijective (Homomorphisms.Polynomial.Construction.expansionLift R n) (Homomorphisms.Polynomial.Construction.expansionEquiv R n).bijective
  have hc := ho.comp hl
  simpa only [Homomorphisms.Polynomial.Construction.expansionLift, AdjoinRoot.lift_comp_of, mul_one] using hc

theorem RingHomHasFiniteBasis.of_comp_bijective_right
    {f : R →+* S} {g : S →+* T} {n : ℕ}
    (h : RingHomHasFiniteBasis (g.comp f) n) (hf : Function.Bijective f) :
    RingHomHasFiniteBasis g n := by
  let e := RingEquiv.ofBijective f hf
  have he : (g.comp f).comp e.symm.toRingHom = g := by
    ext x
    exact congrArg g (e.apply_symm_apply x)
  have hc := (ringHomHasFiniteBasis_of_bijective e.symm.toRingHom e.symm.bijective).comp h
  rw [he, one_mul] at hc
  exact hc

theorem RingHomHasFiniteBasis.of_comp_bijective_left
    {f : R →+* S} {g : S →+* T} {n : ℕ}
    (h : RingHomHasFiniteBasis (g.comp f) n) (hg : Function.Bijective g) :
    RingHomHasFiniteBasis f n := by
  let e := RingEquiv.ofBijective g hg
  have he : e.symm.toRingHom.comp (g.comp f) = f := by
    ext x
    exact e.symm_apply_apply (f x)
  have hc := h.comp (ringHomHasFiniteBasis_of_bijective e.symm.toRingHom e.symm.bijective)
  rw [he, mul_one] at hc
  exact hc

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteFreeRank
