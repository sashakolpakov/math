import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.SquareZeroAlgebraComparison

/-! # Square Zero Map Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.SquareZeroMapIsomorphism

noncomputable section

/-! An actual map to a formally smooth algebra that becomes an
isomorphism modulo a square-zero base ideal is already an isomorphism.
The resulting algebra equivalence retains the given map exactly. -/

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra.FormallySmooth R T]

theorem smooth_algebraHom_bijective_of_reduction_equiv
    (I : Ideal R) (hI : I * I = ⊥)
    (e : (S ⧸ I.map (algebraMap R S)) ≃ₐ[R] (T ⧸ I.map (algebraMap R T)))
    (f : S →ₐ[R] T)
    (hf : (Ideal.Quotient.mkₐ R (I.map (algebraMap R T))).comp f =
      e.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R S)))) :
    Function.Bijective f := by
  let J := I.map (algebraMap R S)
  let K := I.map (algebraMap R T)
  let qS := Ideal.Quotient.mkₐ R J
  let qT := Ideal.Quotient.mkₐ R K
  have hJ : IsNilpotent J := by
    refine ⟨2, ?_⟩
    change (I.map (algebraMap R S)) ^ 2 = ⊥
    rw [pow_two, ← Ideal.map_mul, hI, Ideal.map_bot]
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J hJ (e.symm.toAlgHom.comp qT)
  have hf' (s : S) : qT (f s) = e (qS s) := AlgHom.congr_fun hf s
  have hg' (t : T) : qS (g t) = e.symm (qT t) := AlgHom.congr_fun hg t
  apply RepresentationTheory.Theta.Geometric.SquareZero.LinearIsomorphisms.linear_bijective_of_squareZero_inverse I hI f.toLinearMap g.toLinearMap
  · intro s
    rw [Ideal.smul_top_eq_map]
    change g (f s) - s ∈ J
    apply (Ideal.Quotient.eq (I := J)).mp
    change qS (g (f s)) = qS s
    rw [hg', hf', e.symm_apply_apply]
  · intro t
    rw [Ideal.smul_top_eq_map]
    change f (g t) - t ∈ K
    apply (Ideal.Quotient.eq (I := K)).mp
    change qT (f (g t)) = qT t
    rw [hf', hg', e.apply_symm_apply]

def smoothAlgebraEquivOfReductionEquiv
    (I : Ideal R) (hI : I * I = ⊥)
    (e : (S ⧸ I.map (algebraMap R S)) ≃ₐ[R] (T ⧸ I.map (algebraMap R T)))
    (f : S →ₐ[R] T)
    (hf : (Ideal.Quotient.mkₐ R (I.map (algebraMap R T))).comp f =
      e.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R S)))) : S ≃ₐ[R] T :=
  AlgEquiv.ofBijective f (smooth_algebraHom_bijective_of_reduction_equiv I hI e f hf)

theorem smoothAlgebraEquivOfReductionEquiv_toAlgHom
    (I : Ideal R) (hI : I * I = ⊥)
    (e : (S ⧸ I.map (algebraMap R S)) ≃ₐ[R] (T ⧸ I.map (algebraMap R T)))
    (f : S →ₐ[R] T)
    (hf : (Ideal.Quotient.mkₐ R (I.map (algebraMap R T))).comp f =
      e.toAlgHom.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R S)))) :
    (smoothAlgebraEquivOfReductionEquiv I hI e f hf).toAlgHom = f := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.SquareZeroMapIsomorphism
