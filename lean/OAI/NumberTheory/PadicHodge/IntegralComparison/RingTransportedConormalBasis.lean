import OAI.NumberTheory.PadicHodge.IntegralComparison.DualCoordinateConormalBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConormalKoszulPurity

/-! # Ring Transported Conormal Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RingTransportedConormalBasis

noncomputable section

/-! A ring isomorphism transports generators with dual derivations to
a matching basis of the actual conormal module. Restricting derivations
to the integers is sufficient for this basis certificate. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

variable {k : Type u} {R : Type v} {S : Type w}
  [CommRing k] [CommRing R] [CommRing S] [Algebra k S]
  (e : R ≃+* S)

def derivation (D : Derivation k S S) : Derivation ℤ R R where
  toLinearMap :=
    (e.symm.toAddMonoidHom.comp (D.toLinearMap.toAddMonoidHom.comp e.toAddMonoidHom)).toIntLinearMap
  map_one_eq_zero' := by
    change e.symm (D (e 1)) = 0
    simp only [map_one, Derivation.map_one_eq_zero, map_zero]
  leibniz' a b := by
    change e.symm (D (e (a * b))) = a * e.symm (D (e b)) + b * e.symm (D (e a))
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, RingEquiv.symm_apply_apply]

@[simp]
theorem derivation_apply (D : Derivation k S S) (x : R) : derivation e D x = e.symm (D (e x)) := rfl

variable {n : ℕ} (I : Ideal R) (z : Fin n → S) (D : Fin n → Derivation k S S)
  (hD : ∀ i j, D i (z j) = if i = j then 1 else 0)
  (hI : I.map e.toRingHom = Ideal.span (Set.range z))

include hI in
theorem generates : Ideal.span (Set.range (fun i => e.symm (z i))) = I := by
  have h := congrArg (fun J : Ideal S => J.map e.symm.toRingHom) hI
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
    ext x
    exact e.symm_apply_apply x
  rw [Ideal.map_map, he, Ideal.map_id, Ideal.map_span, ← Set.range_comp] at h
  simpa only [Function.comp_def, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom] using h.symm

def vectors (i : Fin n) : I :=
  ⟨e.symm (z i), generates e I z hI ▸ Ideal.subset_span (Set.mem_range_self i)⟩

include hD hI in
theorem coordinates (i j : Fin n) :
    derivation e (D i) (vectors e I z hI j).val = if i = j then 1 else 0 := by
  change e.symm (D i (e (e.symm (z j)))) = _
  rw [RingEquiv.apply_symm_apply, hD]
  split_ifs <;> simp only [map_one, map_zero]

def basis : Module.Basis (Fin n) (R ⧸ I) I.Cotangent :=
  DualCoordinateConormalBasis.basis (k := ℤ) I (vectors e I z hI)
    (fun i => derivation e (D i)) (coordinates e I z D hD hI) (generates e I z hI)

theorem basis_apply (i : Fin n) :
    basis e I z D hD hI i = I.toCotangent (vectors e I z hI i) :=
  DualCoordinateConormalBasis.basis_apply _ _ _ _ _ i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RingTransportedConormalBasis
