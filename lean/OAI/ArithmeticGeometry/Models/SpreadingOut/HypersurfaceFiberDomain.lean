import OAI.ArithmeticGeometry.Models.SpreadingOut.RootScalarExtension
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Hypersurface Fiber Domain -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceFiberDomain.Construction

noncomputable section

/-! Geometrically integral fibers of a localized monic hypersurface. -/

open scoped TensorProduct

universe u

theorem root_isDomain_of_flatten_irreducible
    (k : Type u) [Field k] (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) k))
    (hp : Irreducible ((MvPolynomial.finSuccEquiv k n).symm p)) : IsDomain (AdjoinRoot p) := by
  let q := (MvPolynomial.finSuccEquiv k n).symm p
  have : (Ideal.span ({q} : Set (MvPolynomial (Fin (n + 1)) k))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hp.prime
  let e := PolynomialCoordinates.Construction.polynomialHypersurfaceIso k n p
  exact Function.Injective.isDomain e.symm.toRingHom e.symm.injective

theorem localized_monic_hypersurface_fiber_domain
    (R k : Type u) [CommRing R] [Field k] [Algebra R k]
    (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) R))
    (hp : p.Monic) (hdegree : 0 < p.natDegree) (d : MvPolynomial (Fin n) R)
    (hirr : Irreducible (MvPolynomial.map (algebraMap R k)
      ((MvPolynomial.finSuccEquiv R n).symm p)))
    (hd : MvPolynomial.map (algebraMap R k) d ≠ 0) :
    IsDomain (k ⊗[R] Localization.Away
      (algebraMap (MvPolynomial (Fin n) R) (AdjoinRoot p) d)) := by
  let p' := Polynomial.map (MvPolynomial.map (algebraMap R k)) p
  have hirr' : Irreducible ((MvPolynomial.finSuccEquiv k n).symm p') := by
    rw [← PolynomialCoordinates.Construction.map_finSuccEquiv_symm]
    exact hirr
  have : IsDomain (AdjoinRoot p') := root_isDomain_of_flatten_irreducible k n p' hirr'
  let e := RootScalarExtension.Construction.rootScalarExtensionIso R k n p
  have : IsDomain (k ⊗[R] AdjoinRoot p) :=
    Function.Injective.isDomain e.toRingHom e.injective
  have hdeg' : p'.degree ≠ 0 := by
    apply ne_of_gt
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [show p'.natDegree = p.natDegree from hp.natDegree_map _]
    exact hdegree
  have hcoeff : Function.Injective (algebraMap (MvPolynomial (Fin n) k) (AdjoinRoot p')) :=
    AdjoinRoot.of.injective_of_degree_ne_zero hdeg'
  let c := algebraMap (MvPolynomial (Fin n) R) (AdjoinRoot p) d
  have hc : (1 ⊗ₜ[R] c : k ⊗[R] AdjoinRoot p) ≠ 0 := by
    intro hc
    have H := congrArg e hc
    rw [map_zero] at H
    change e (1 ⊗ₜ[R] algebraMap _ (AdjoinRoot p) d) = 0 at H
    rw [RootScalarExtension.Construction.rootScalarExtensionIso_one_tmul_algebraMap] at H
    exact hd (hcoeff (H.trans (map_zero _).symm))
  have : IsDomain (Localization.Away (1 ⊗ₜ[R] c : k ⊗[R] AdjoinRoot p)) :=
    Localization.Away.isDomain hc
  let e' := IsLocalization.Away.tensorProductEquivTMulRight R k c (Localization.Away c)
  exact Function.Injective.isDomain e'.toRingHom e'.injective

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceFiberDomain.Construction
