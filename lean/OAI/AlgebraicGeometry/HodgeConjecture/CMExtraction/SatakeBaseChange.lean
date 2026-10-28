import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RadialSatake
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadial

/-! # Satake Base Change -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa

noncomputable section

section

/-! Evaluate the actual rational Satake transform over any coefficient
field. Base change and Galois conjugation act on the actual torus point. -/

open scoped Classical TensorProduct

def torusCharacterOver {k : Type*} [CommRing k] (t : Fin 3 → kˣ) :
    Multiplicative (Fin 3 → ℤ) →* kˣ where
  toFun ell := ∏ i, t i ^ ell.toAdd i
  map_one' := by simp
  map_mul' a b := by
    change (∏ i, t i ^ (a.toAdd i + b.toAdd i)) = _
    simp only [zpow_add, Finset.prod_mul_distrib]

theorem torusCharacterOver_map {k l : Type*} [CommRing k] [CommRing l]
    (j : k →+* l) (t : Fin 3 → kˣ) (ell : Multiplicative (Fin 3 → ℤ)) :
    j (torusCharacterOver t ell : k) =
      (torusCharacterOver (fun i => Units.map j.toMonoidHom (t i)) ell : l) := by
  simp [torusCharacterOver, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg (fun u : lˣ => (u : l))
    (map_zpow (Units.map j.toMonoidHom) (t i) (ell.toAdd i))

def rationalLatticeEvaluation {k : Type*} [Field k] [Algebra ℚ k] (t : Fin 3 → kˣ) :
    AddMonoidAlgebra ℚ (Fin 3 → ℤ) →ₐ[ℚ] k :=
  AddMonoidAlgebra.lift ℚ k (Fin 3 → ℤ) ((Units.coeHom k).comp (torusCharacterOver t))

theorem rationalLatticeEvaluation_map {k l : Type*} [Field k] [Field l]
    [Algebra ℚ k] [Algebra ℚ l] (j : k →ₐ[ℚ] l) (t : Fin 3 → kˣ)
    (f : AddMonoidAlgebra ℚ (Fin 3 → ℤ)) :
    j (rationalLatticeEvaluation t f) =
      rationalLatticeEvaluation (fun i => Units.map j.toMonoidHom (t i)) f := by
  unfold rationalLatticeEvaluation
  rw [AddMonoidAlgebra.lift_apply', AddMonoidAlgebra.lift_apply', map_finsuppSum]
  apply Finsupp.sum_congr
  intro ell _
  rw [map_mul, j.commutes]
  congr 1
  exact torusCharacterOver_map j.toRingHom t (Multiplicative.ofAdd ell)

theorem rationalLatticeEvaluation_complex (t : Fin 3 → ℂˣ)
    (f : AddMonoidAlgebra ℚ (Fin 3 → ℤ)) :
    rationalLatticeEvaluation t f =
      SatakeKernel.Iwasawa.evaluateLattice ((Units.coeHom ℂ).comp (SatakeParameters.Iwasawa.torusCharacter t))
        (AddMonoidAlgebra.mapRingHom (Fin 3 → ℤ) (algebraMap ℚ ℂ) f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single ell c =>
    rw [AddMonoidAlgebra.mapRingHom_single, SatakeKernel.Iwasawa.evaluateLattice_single]
    exact AddMonoidAlgebra.lift_single _ ell c

variable (q : ℕ) [Fact q.Prime]

def torusSatakeOver {k : Type*} [Field k] [Algebra ℚ k] (t : Fin 3 → kˣ) :
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[ℚ] k :=
  (rationalLatticeEvaluation t).comp (RadialSatake.Iwasawa.rationalSatake q)

theorem torusSatakeOver_map {k l : Type*} [Field k] [Field l]
    [Algebra ℚ k] [Algebra ℚ l] (j : k →ₐ[ℚ] l) (t : Fin 3 → kˣ)
    (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    j (torusSatakeOver q t T) =
      torusSatakeOver q (fun i => Units.map j.toMonoidHom (t i)) T :=
  rationalLatticeEvaluation_map j t (RadialSatake.Iwasawa.rationalSatake q T)

theorem torusSatakeOver_complex (t : Fin 3 → ℂˣ) (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    torusSatakeOver q t T =
      SatakeKernel.Iwasawa.evaluateLattice ((Units.coeHom ℂ).comp (SatakeParameters.Iwasawa.torusCharacter t))
        (RadialSatake.Iwasawa.normalizedSatake q ((1 : ℂ) ⊗ₜ[ℚ] T)) := by
  unfold torusSatakeOver
  rw [AlgHom.comp_apply, rationalLatticeEvaluation_complex, RadialSatake.Iwasawa.rationalSatake_scalar_extension]

end

/-! The actual SL3 transform has support on the determinant-zero lattice,
so a common scalar on its torus coordinates does not change its character. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]

theorem rationalSatake_support_sum (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (ell : Fin 3 → ℤ)
    (h : ell ∈ (RadialSatake.Iwasawa.rationalSatake q T).coeff.support) : ∑ i, ell i = 0 := by
  have hc : RadialSatake.Iwasawa.rationalSatakeCoefficients q T ell ≠ 0 := Finsupp.mem_support_iff.mp h
  change Finsupp.mapDomain (Borel.Iwasawa.decomposition q).height
    (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T) ell * (q : ℚ) ^ (ell 2 - ell 0) ≠ 0 at hc
  obtain ⟨x, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero (mul_ne_zero_iff.mp hc).1
  exact Borel.Iwasawa.height_sum q x

theorem torusCharacterOver_scale {k : Type*} [CommRing k] (c : kˣ) (t : Fin 3 → kˣ)
    (ell : Fin 3 → ℤ) (h : ∑ i, ell i = 0) :
    torusCharacterOver (fun i => c * t i) (Multiplicative.ofAdd ell) =
      torusCharacterOver t (Multiplicative.ofAdd ell) := by
  change (∏ i, (c * t i) ^ ell i) = ∏ i, t i ^ ell i
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [Fin.prod_univ_three, ← zpow_add, ← zpow_add]
  have hs : ell 0 + ell 1 + ell 2 = 0 := by simpa only [Fin.sum_univ_three] using h
  rw [hs, zpow_zero, one_mul]

theorem torusSatakeOver_scale {k : Type*} [Field k] [Algebra ℚ k]
    (c : kˣ) (t : Fin 3 → kˣ) :
    torusSatakeOver q (fun i => c * t i) = torusSatakeOver q t := by
  apply AlgHom.ext
  intro T
  change rationalLatticeEvaluation _ (RadialSatake.Iwasawa.rationalSatake q T) = rationalLatticeEvaluation _ (RadialSatake.Iwasawa.rationalSatake q T)
  unfold rationalLatticeEvaluation
  rw [AddMonoidAlgebra.lift_apply', AddMonoidAlgebra.lift_apply']
  apply Finsupp.sum_congr
  intro ell hell
  change algebraMap ℚ k _ * (torusCharacterOver (fun i => c * t i) (Multiplicative.ofAdd ell) : k) = _
  rw [torusCharacterOver_scale c t ell (rationalSatake_support_sum q T ell hell)]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa
