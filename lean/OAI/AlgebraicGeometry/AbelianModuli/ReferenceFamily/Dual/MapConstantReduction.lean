import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.Derivation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients

/-! # Map Constant Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MapConstantReduction

noncomputable section

section

/-! An actual map of dual-number products fixing the base parameter
transports differences between lifts by its original reduced map.
The extra first-order term cancels for lifts with the same reduction. -/

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (q : A →ₐ[k] B)
    (f : DualNumber A →ₐ[k] DualNumber B)
    (hred : ∀ u, (f u).fst = q u.fst)
    (heps : f DualNumber.eps = DualNumber.eps)

include hred heps

theorem dualMap_inr (a : A) : f (TrivSqZeroExt.inr a) = TrivSqZeroExt.inr (q a) := by
  have ha : (TrivSqZeroExt.inr a : DualNumber A) =
      TrivSqZeroExt.inl a * DualNumber.eps := by
    apply TrivSqZeroExt.ext <;> simp
  rw [ha, map_mul, heps]
  apply TrivSqZeroExt.ext
  · simp
  · simp only [DualNumber.snd_mul, DualNumber.snd_eps, DualNumber.fst_eps,
      mul_one, mul_zero, add_zero, TrivSqZeroExt.snd_inr]
    exact hred (TrivSqZeroExt.inl a)

theorem dualMap_sameReduction_difference (u v : DualNumber A) (h : u.fst = v.fst) :
    (f u).snd - (f v).snd = q (u.snd - v.snd) := by
  have huv : u - v = TrivSqZeroExt.inr (u.snd - v.snd) := by
    apply TrivSqZeroExt.ext
    · exact sub_eq_zero.mpr h
    · rfl
  have hm := congrArg TrivSqZeroExt.snd (congrArg f huv)
  rw [map_sub, dualMap_inr q f hred heps] at hm
  exact hm

end

/-! On a dual-number element whose reduction is a base scalar, an
actual deformed coefficient map equals its ordinary coefficient map.
The deformation term vanishes on that original scalar. -/

variable {k C D : Type*} [CommRing k] [CommRing C] [CommRing D]
    [Algebra k C] [Algebra k D] (q : C →ₐ[k] D)
    (f : DualNumber C →ₐ[k] DualNumber D)
    (hred : ∀ u, (f u).fst = q u.fst)
    (heps : f DualNumber.eps = DualNumber.eps)

include hred heps

theorem dualMap_constantReduction (u : DualNumber C) (r : k) (h : u.fst = algebraMap k C r) :
    f u = NumberCoefficients.dualNumberAlgMap q u := by
  have hu : u = algebraMap k (DualNumber C) r + TrivSqZeroExt.inr u.snd := by
    rw [IsScalarTower.algebraMap_apply k C (DualNumber C), TrivSqZeroExt.algebraMap_eq_inl]
    apply TrivSqZeroExt.ext
    · simpa only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero] using h
    · simp
  rw [hu, map_add, map_add, f.commutes, (NumberCoefficients.dualNumberAlgMap q).commutes,
    dualMap_inr q f hred heps]
  congr 1
  apply TrivSqZeroExt.ext
  · exact (map_zero q).symm
  · rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.MapConstantReduction
