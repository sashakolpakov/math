import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenTangentDifferences

/-! # Coefficient Unit Logarithms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms

noncomputable section

/-! Logarithmic derivatives of actual units with coefficients in a
fiber algebra. They are additive on units, linear in the derivation,
and commute with the original coefficient restriction squares. -/

variable {k S B : Type*} [CommRing k] [CommRing S] [CommRing B]
    [Algebra k S] [Algebra k B] [Algebra S B] [IsScalarTower k S B]

def coefficientUnitLog (d : Derivation k S B) (u : Sˣ) : B :=
  d u.val * algebraMap S B (u⁻¹).val

omit [IsScalarTower k S B] in
theorem coefficientUnitLog_one (d : Derivation k S B) :
    coefficientUnitLog d 1 = 0 := by
  change d 1 * algebraMap S B 1 = 0
  rw [Derivation.map_one_eq_zero, zero_mul]

omit [IsScalarTower k S B] in
theorem coefficientUnitLog_mul (d : Derivation k S B) (u v : Sˣ) :
    coefficientUnitLog d (u * v) = coefficientUnitLog d u + coefficientUnitLog d v := by
  have hi (w : Sˣ) : algebraMap S B w.val * algebraMap S B (w⁻¹).val = 1 := by
    exact ((map_mul (algebraMap S B) w.val (w⁻¹).val).symm.trans
      (congrArg (algebraMap S B) w.val_inv)).trans (map_one (algebraMap S B))
  unfold coefficientUnitLog
  change d (u.val * v.val) * algebraMap S B ((u * v)⁻¹).val = _
  rw [d.leibniz, mul_inv_rev]
  simp only [Units.val_mul, map_mul, Algebra.smul_def]
  calc
    _ = d v.val * (algebraMap S B u.val * algebraMap S B (u⁻¹).val) *
          algebraMap S B (v⁻¹).val +
        d u.val * (algebraMap S B v.val * algebraMap S B (v⁻¹).val) *
          algebraMap S B (u⁻¹).val := by ring
    _ = _ := by rw [hi u, hi v, mul_one, mul_one, add_comm]

def coefficientUnitLogLinear (u : Sˣ) : Derivation k S B →ₗ[k] B where
  toFun d := coefficientUnitLog d u
  map_add' d e := by
    change (d u.val + e u.val) * _ = _
    exact add_mul _ _ _
  map_smul' c d := by
    change (c • d u.val) * _ = _
    exact smul_mul_assoc _ _ _

theorem coefficientUnitLog_sub (d e : Derivation k S B) (u : Sˣ) :
    coefficientUnitLog (d - e) u = coefficientUnitLog d u - coefficientUnitLog e u :=
  (coefficientUnitLogLinear u).map_sub d e

variable {S' B' : Type*} [CommRing S'] [CommRing B']
    [Algebra k S'] [Algebra k B'] [Algebra S' B'] [IsScalarTower k S' B']

omit [IsScalarTower k S B] [IsScalarTower k S' B'] in
theorem coefficientUnitLog_map (f : S →ₐ[k] S') (F : B →ₐ[k] B')
    (hF : ∀ a, F (algebraMap S B a) = algebraMap S' B' (f a))
    (d : Derivation k S B) (e : Derivation k S' B') (he : ∀ a, e (f a) = F (d a)) (u : Sˣ) :
    coefficientUnitLog e (Units.map f.toMonoidHom u) = F (coefficientUnitLog d u) := by
  change e (f u.val) * algebraMap S' B' (f (u⁻¹).val) = F (d u.val * algebraMap S B (u⁻¹).val)
  rw [he, ← hF, map_mul]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms
