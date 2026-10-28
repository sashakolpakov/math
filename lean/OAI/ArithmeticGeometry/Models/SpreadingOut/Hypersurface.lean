import OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceFiberDomain

/-! # Hypersurface -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Hypersurface.Construction

noncomputable section

/-! After removing one nonzero base element, all field fibers of an
absolutely irreducible monic hypersurface chart are integral. -/

open scoped TensorProduct

universe u

theorem localized_hypersurface_domain_after_inverting_base_element
    (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) R))
    (hp : p.Monic) (hdegree : 0 < p.natDegree)
    (d : MvPolynomial (Fin n) R) (hd : d ≠ 0)
    (hirr : Irreducible (MvPolynomial.map (algebraMap R (AlgebraicClosure K))
      ((MvPolynomial.finSuccEquiv R n).symm p))) :
    ∃ r : R, r ≠ 0 ∧
      ∀ (k : Type u) [Field k] [Algebra R k], algebraMap R k r ≠ 0 →
        IsDomain (k ⊗[R] Localization.Away
          (algebraMap (MvPolynomial (Fin n) R) (AdjoinRoot p) d)) := by
  obtain ⟨r, hr, hgood⟩ := AbsoluteIrreducibility.Construction.absolute_irreducibility_after_inverting_nonzero
    (R := R) (K := K) ((MvPolynomial.finSuccEquiv R n).symm p) hirr
  obtain ⟨m, hm⟩ := MvPolynomial.exists_coeff_ne_zero hd
  refine ⟨r * AddMonoidAlgebra.coeff (d) (m), mul_ne_zero hr hm, fun k _ _ hk ↦ ?_⟩
  rw [map_mul, mul_ne_zero_iff] at hk
  apply HypersurfaceFiberDomain.Construction.localized_monic_hypersurface_fiber_domain R k n p hp hdegree d
    (hgood k (algebraMap R k) hk.1)
  intro h
  have H := congrArg ((fun p => AddMonoidAlgebra.coeff p (m))) h
  rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at H
  exact hk.2 H

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Hypersurface.Construction
