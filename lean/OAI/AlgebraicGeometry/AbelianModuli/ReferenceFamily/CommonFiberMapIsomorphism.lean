import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.SquareZeroMapIsomorphism

/-! # Common Fiber Map Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonFiberMapIsomorphism

noncomputable section

/-! A map between square-zero deformations with the same identified
fiber is an isomorphism when its target is formally smooth. Its given
underlying map is retained. -/

variable {R P T B : Type*} [CommRing R] [CommRing P] [CommRing T] [CommRing B]
    [Algebra R P] [Algebra R T] [Algebra R B] [Algebra.FormallySmooth R T]
    (I : Ideal R) (hI : I * I = ⊥)
    (eP : (P ⧸ I.map (algebraMap R P)) ≃ₐ[R] B)
    (eT : (T ⧸ I.map (algebraMap R T)) ≃ₐ[R] B)
    (f : P →ₐ[R] T)
    (h : ∀ p : P, eT (Ideal.Quotient.mk (I.map (algebraMap R T)) (f p)) =
      eP (Ideal.Quotient.mk (I.map (algebraMap R P)) p))

include hI h in
theorem commonFiberMap_bijective : Function.Bijective f := by
  apply Smooth.SquareZeroMapIsomorphism.smooth_algebraHom_bijective_of_reduction_equiv I hI (eP.trans eT.symm) f
  apply AlgHom.ext
  intro p
  apply eT.injective
  change eT (Ideal.Quotient.mk (I.map (algebraMap R T)) (f p)) =
    eT (eT.symm (eP (Ideal.Quotient.mk (I.map (algebraMap R P)) p)))
  rw [eT.apply_symm_apply]
  exact h p

def commonFiberMapEquiv : P ≃ₐ[R] T :=
  AlgEquiv.ofBijective f (commonFiberMap_bijective I hI eP eT f h)

theorem commonFiberMapEquiv_toAlgHom : (commonFiberMapEquiv I hI eP eT f h).toAlgHom = f := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonFiberMapIsomorphism
