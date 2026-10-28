import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms

/-! # Derivation Transport -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DerivationTransport.PDDerivationTransport

noncomputable section

/-!
# Transporting divided-power derivations through algebra equivalences

Conjugating an actual derivation by an algebra equivalence preserves the
Leibniz rule and the divided-power rule. This transfers coordinate
derivatives between polynomial envelopes and divided-monomial algebras.
-/

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (d : Derivation R A A)

def conjugate : Derivation R B B where
  toFun b := e (d (e.symm b))
  map_add' a b := by simp only [map_add]
  map_smul' r a := by
    change e (d.toLinearMap (e.symm (r • a))) = r • e (d.toLinearMap (e.symm a))
    rw [map_smul, map_smul, map_smul]
  map_one_eq_zero' := by
    change e (d (e.symm 1)) = 0
    simp only [map_one, Derivation.map_one_eq_zero, map_zero]
  leibniz' a b := by
    change e (d (e.symm (a * b))) = a * e (d (e.symm b)) + b * e (d (e.symm a))
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, AlgEquiv.apply_symm_apply]

theorem conjugate_apply (b : B) : conjugate R A B e d b = e (d (e.symm b)) := rfl

theorem conjugate_apply_equiv (a : A) : conjugate R A B e d (e a) = e (d a) := by
  rw [conjugate_apply, AlgEquiv.symm_apply_apply]

variable (I : Ideal A) (J : Ideal B) (δ : DividedPowers I) (ε : DividedPowers J)
  (he : DividedPowers.IsDPMorphism ε δ e.symm.toRingHom)
  (hd : ∀ n a, a ∈ I → d (δ.dpow (n + 1) a) = δ.dpow n a * d a)

include he hd in
theorem conjugate_dpow (n : ℕ) {b : B} (hb : b ∈ J) :
    conjugate R A B e d (ε.dpow (n + 1) b) = ε.dpow n b * conjugate R A B e d b := by
  have ha : e.symm b ∈ I := he.ideal_comp (Ideal.mem_map_of_mem e.symm.toRingHom hb)
  have hpow (m : ℕ) : e.symm (ε.dpow m b) = δ.dpow m (e.symm b) := he.map_dpow hb
  change e (d (e.symm (ε.dpow (n + 1) b))) = ε.dpow n b * e (d (e.symm b))
  rw [hpow, hd n (e.symm b) ha, map_mul, ← hpow n,
    AlgEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DerivationTransport.PDDerivationTransport
