import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Unit Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCoordinates

noncomputable section

/-! The exact additive coordinates of units with constant coefficient
one, including products, inverses, and changes of coefficient ring. -/

variable {R S : Type*} [CommRing R] [CommRing S]

def normalizedDualUnit (a : R) : (DualNumber R)ˣ where
  val := (1, a)
  inv := (1, -a)
  val_inv := by
    apply TrivSqZeroExt.ext
    · exact one_mul 1
    · change 1 * (-a) + a * 1 = 0
      rw [one_mul, mul_one, neg_add_cancel]
  inv_val := by
    apply TrivSqZeroExt.ext
    · exact one_mul 1
    · change 1 * a + (-a) * 1 = 0
      rw [one_mul, mul_one, add_neg_cancel]

theorem normalizedDualUnit_add (a b : R) :
    normalizedDualUnit (a + b) = normalizedDualUnit a * normalizedDualUnit b := by
  apply Units.ext
  apply TrivSqZeroExt.ext
  · exact (one_mul 1).symm
  · change a + b = 1 * b + a * 1
    rw [one_mul, mul_one, add_comm]

theorem normalizedDualUnit_recover (u : (DualNumber R)ˣ) (hu : u.val.fst = 1) :
    normalizedDualUnit u.val.snd = u := by
  apply Units.ext
  exact TrivSqZeroExt.ext hu.symm rfl

theorem normalizedDualUnit_map (f : R →+* S) (a : R) :
    Units.map (NumberCoefficients.dualNumberRingMap f).toMonoidHom (normalizedDualUnit a) =
      normalizedDualUnit (f a) := by
  apply Units.ext
  apply TrivSqZeroExt.ext
  · exact map_one f
  · rfl

theorem dualUnit_snd_mul (u v : (DualNumber R)ˣ) (hu : u.val.fst = 1) (hv : v.val.fst = 1) :
    (u * v).val.snd = u.val.snd + v.val.snd := by
  change u.val.fst * v.val.snd + u.val.snd * v.val.fst = _
  rw [hu, hv, one_mul, mul_one, add_comm]

theorem dualUnit_fst_inv (u : (DualNumber R)ˣ) (hu : u.val.fst = 1) :
    (u⁻¹).val.fst = 1 := by
  have h := congrArg TrivSqZeroExt.fst u.val_inv
  change u.val.fst * (u⁻¹).val.fst = 1 at h
  simpa only [hu, one_mul] using h

theorem dualUnit_snd_inv (u : (DualNumber R)ˣ) (hu : u.val.fst = 1) :
    (u⁻¹).val.snd = -u.val.snd := by
  have h := congrArg TrivSqZeroExt.snd u.val_inv
  change (u * u⁻¹).val.snd = 0 at h
  rw [dualUnit_snd_mul u u⁻¹ hu (dualUnit_fst_inv u hu)] at h
  exact eq_neg_of_add_eq_zero_right h

theorem dualUnit_snd_div (u v : (DualNumber R)ˣ) (hu : u.val.fst = 1) (hv : v.val.fst = 1) :
    (u / v).val.snd = u.val.snd - v.val.snd := by
  rw [div_eq_mul_inv, dualUnit_snd_mul u v⁻¹ hu (dualUnit_fst_inv v hv), dualUnit_snd_inv v hv,
    sub_eq_add_neg]

theorem dualUnit_fst_div (u v : (DualNumber R)ˣ) (hu : u.val.fst = 1) (hv : v.val.fst = 1) :
    (u / v).val.fst = 1 := by
  change u.val.fst * (v⁻¹).val.fst = 1
  rw [hu, dualUnit_fst_inv v hv, one_mul]

theorem normalizedDualUnits_ext (u v : (DualNumber R)ˣ)
    (hu : u.val.fst = 1) (hv : v.val.fst = 1) (h : u.val.snd = v.val.snd) : u = v :=
  (normalizedDualUnit_recover u hu).symm.trans
    ((congrArg normalizedDualUnit h).trans (normalizedDualUnit_recover v hv))

theorem dualUnit_snd_gauge (u a b : (DualNumber R)ˣ)
    (hu : u.val.fst = 1) (ha : a.val.fst = 1) (hb : b.val.fst = 1) :
    (u * b / a).val.snd = u.val.snd + b.val.snd - a.val.snd := by
  have hub : (u * b).val.fst = 1 := by
    change u.val.fst * b.val.fst = 1
    rw [hu, hb, one_mul]
  rw [dualUnit_snd_div _ _ hub ha, dualUnit_snd_mul _ _ hu hb]

def normalizedDualUnitKernel (R : Type*) [CommRing R] : Subgroup (DualNumber R)ˣ :=
  (Units.map (TrivSqZeroExt.fstHom R R R).toMonoidHom).ker

theorem normalizedDualUnitKernel_mem (u : (DualNumber R)ˣ) :
    u ∈ normalizedDualUnitKernel R ↔ u.val.fst = 1 := by
  change Units.map (TrivSqZeroExt.fstHom R R R).toMonoidHom u = 1 ↔ _
  exact Units.ext_iff

def normalizedDualUnitEquiv (R : Type*) [CommRing R] :
    R ≃+ Additive (normalizedDualUnitKernel R) where
  toFun a := Additive.ofMul ⟨normalizedDualUnit a, (normalizedDualUnitKernel_mem _).mpr rfl⟩
  invFun u := u.toMul.val.val.snd
  left_inv _ := rfl
  right_inv u := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact normalizedDualUnit_recover u.toMul.val ((normalizedDualUnitKernel_mem _).mp u.toMul.property)
  map_add' a b := by
    apply Additive.toMul.injective
    exact Subtype.ext (normalizedDualUnit_add a b)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnitCoordinates
