import Mathlib

/-! # Alternating Polarization -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.Lattice

/-! Integral alternating-form reduction for the reference polarization.
The least nonzero pairing splits off an integral rank-two block. These
lemmas concern the actual bilinear form, not a chosen polarization type. -/

open scoped Classical

variable {M : Type*} [AddCommGroup M]

def IsMinimalPair (B : LinearMap.BilinForm ℤ M) (d : ℤ) (x y : M) : Prop :=
  0 < d ∧ B x y = d ∧ ∀ u v, B u v ≠ 0 → d ≤ |B u v|

theorem exists_minimal_pair (B : LinearMap.BilinForm ℤ M)
    (hne : ∃ x y, B x y ≠ 0) :
    ∃ (d : ℤ) (x y : M), IsMinimalPair B d x y := by
  have hpos : ∀ x y, B x y ≠ 0 →
      ∃ u v, B u v = (B x y).natAbs := by
    intro x y _
    by_cases hxy : 0 ≤ B x y
    · exact ⟨x, y, by simp only [Int.natCast_natAbs, abs_of_nonneg hxy]⟩
    · refine ⟨x, -y, ?_⟩
      rw [map_neg, Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hxy)]
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ x y, B x y = (n : ℤ) := by
    obtain ⟨x, y, hxy⟩ := hne
    exact ⟨(B x y).natAbs, Int.natAbs_pos.mpr hxy, hpos x y hxy⟩
  obtain ⟨x, y, hxy⟩ := (Nat.find_spec hex).2
  refine ⟨Nat.find hex, x, y, by exact_mod_cast (Nat.find_spec hex).1, hxy, ?_⟩
  intro u v huv
  have hmin := Nat.find_min' hex
    (show 0 < (B u v).natAbs ∧ ∃ x y, B x y = ((B u v).natAbs : ℤ) from
      ⟨Int.natAbs_pos.mpr huv, hpos u v huv⟩)
  rw [← Int.natCast_natAbs]
  exact_mod_cast hmin

theorem minimal_pair_dvd_left (B : LinearMap.BilinForm ℤ M)
    {d : ℤ} {x y : M} (h : IsMinimalPair B d x y) (z : M) : d ∣ B x z := by
  have heq : B x (z - (B x z / d) • y) = B x z % d := by
    rw [map_sub, map_zsmul, h.2.1]
    simpa only [smul_eq_mul, mul_comm] using (Int.emod_def (B x z) d).symm
  apply Int.dvd_iff_emod_eq_zero.mpr
  by_contra hrem
  have hn := h.2.2 x (z - (B x z / d) • y) (by rwa [heq])
  rw [heq, abs_of_nonneg (Int.emod_nonneg _ h.1.ne')] at hn
  exact (not_lt_of_ge hn) (Int.emod_lt_of_pos _ h.1)

theorem minimal_pair_dvd_right (B : LinearMap.BilinForm ℤ M)
    {d : ℤ} {x y : M} (h : IsMinimalPair B d x y) (z : M) :
    d ∣ B z y := by
  have heq : B (z - (B z y / d) • x) y = B z y % d := by
    rw [map_sub, LinearMap.sub_apply, map_zsmul, LinearMap.smul_apply, h.2.1]
    simpa only [smul_eq_mul, mul_comm] using (Int.emod_def (B z y) d).symm
  apply Int.dvd_iff_emod_eq_zero.mpr
  by_contra hrem
  have hn := h.2.2 (z - (B z y / d) • x) y (by rwa [heq])
  rw [heq, abs_of_nonneg (Int.emod_nonneg _ h.1.ne')] at hn
  exact (not_lt_of_ge hn) (Int.emod_lt_of_pos _ h.1)

def orthogonalRemainder (B : LinearMap.BilinForm ℤ M)
    (d : ℤ) (x y z : M) : M :=
  z - (B z y / d) • x - (B x z / d) • y

theorem remainder_orthogonal (B : LinearMap.BilinForm ℤ M)
    (hB : B.IsAlt) {d : ℤ} {x y : M} (h : IsMinimalPair B d x y) (z : M) :
    B x (orthogonalRemainder B d x y z) = 0 ∧
      B (orthogonalRemainder B d x y z) y = 0 := by
  constructor
  · simp only [orthogonalRemainder, map_sub, map_zsmul, hB x, h.2.1,
      smul_eq_mul, mul_zero, sub_zero]
    rw [Int.ediv_mul_cancel (minimal_pair_dvd_left B h z), sub_self]
  · simp only [orthogonalRemainder, map_sub, LinearMap.sub_apply, map_zsmul,
      LinearMap.smul_apply, hB y, h.2.1, smul_eq_mul, mul_zero, sub_zero]
    rw [Int.ediv_mul_cancel (minimal_pair_dvd_right B h z), sub_self]

theorem minimal_pair_dvd_all (B : LinearMap.BilinForm ℤ M)
    (hB : B.IsAlt) {d : ℤ} {x y : M} (h : IsMinimalPair B d x y)
    (z w : M) : d ∣ B z w := by
  let z' := orthogonalRemainder B d x y z
  let w' := orthogonalRemainder B d x y w
  have hz : B x z' = 0 ∧ B z' y = 0 := remainder_orthogonal B hB h z
  have hw : B x w' = 0 ∧ B w' y = 0 := remainder_orthogonal B hB h w
  have hzx : B z' x = 0 := by
    rw [← hB.neg_eq]
    exact neg_eq_zero.mpr hz.1
  have hyw : B y w' = 0 := by
    rw [← hB.neg_eq]
    exact neg_eq_zero.mpr hw.2
  have hd : d ∣ B z' w' := by
    have heq : B (x + z') (w' - (B z' w' / d) • y) = B z' w' % d := by
      simp only [map_add, LinearMap.add_apply, map_sub, map_zsmul,
        h.2.1, hw.1, hz.2, smul_eq_mul]
      rw [Int.emod_def]
      ring
    apply Int.dvd_iff_emod_eq_zero.mpr
    by_contra hrem
    have hn := h.2.2 (x + z') (w' - (B z' w' / d) • y) (by rwa [heq])
    rw [heq, abs_of_nonneg (Int.emod_nonneg _ h.1.ne')] at hn
    exact (not_lt_of_ge hn) (Int.emod_lt_of_pos _ h.1)
  have hzdecomp : z = z' + (B z y / d) • x + (B x z / d) • y := by
    dsimp [z', orthogonalRemainder]
    abel
  have hwdecomp : w = w' + (B w y / d) • x + (B x w / d) • y := by
    dsimp [w', orthogonalRemainder]
    abel
  rw [hzdecomp, hwdecomp]
  simp only [map_add, LinearMap.add_apply, map_zsmul, LinearMap.smul_apply,
    hz.2, hw.1, hzx, hyw, hB x, hB y, h.2.1, ← hB.neg_eq x y,
    smul_eq_mul, mul_zero, add_zero, zero_add]
  exact dvd_add (dvd_add hd (dvd_mul_of_dvd_right
    (dvd_mul_of_dvd_right (dvd_neg.mpr (dvd_refl d)) _) _))
    (dvd_mul_of_dvd_right (dvd_mul_left d _) _)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.Lattice

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.Split

/-! The integral minimal-pair decomposition as an actual linear
isomorphism, with a nondegenerate alternating orthogonal complement. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.Lattice

variable {M : Type*} [AddCommGroup M]

def dividedFunctional (f : M →ₗ[ℤ] ℤ) (d : ℤ) (hd : d ≠ 0)
    (hdiv : ∀ x, d ∣ f x) : M →ₗ[ℤ] ℤ where
  toFun x := f x / d
  map_add' x y := by
    apply mul_right_cancel₀ hd
    rw [Int.ediv_mul_cancel (hdiv (x + y)), add_mul,
      Int.ediv_mul_cancel (hdiv x), Int.ediv_mul_cancel (hdiv y), map_add]
  map_smul' a x := by
    apply mul_right_cancel₀ hd
    rw [RingHom.id_apply, smul_eq_mul, mul_assoc,
      Int.ediv_mul_cancel (hdiv (a • x)), Int.ediv_mul_cancel (hdiv x), map_zsmul]
    exact smul_eq_mul _ _

def firstCoordinate (B : LinearMap.BilinForm ℤ M)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) : M →ₗ[ℤ] ℤ :=
  dividedFunctional (B.flip y) d h.1.ne' (Lattice.minimal_pair_dvd_right B h)

def secondCoordinate (B : LinearMap.BilinForm ℤ M)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) : M →ₗ[ℤ] ℤ :=
  dividedFunctional (B x) d h.1.ne' (Lattice.minimal_pair_dvd_left B h)

def complement (B : LinearMap.BilinForm ℤ M) (x y : M) : Submodule ℤ M :=
  LinearMap.ker (B x) ⊓ LinearMap.ker (B.flip y)

def remainderMap (B : LinearMap.BilinForm ℤ M)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) : M →ₗ[ℤ] M :=
  LinearMap.id - (firstCoordinate B h).smulRight x - (secondCoordinate B h).smulRight y

theorem remainderMap_apply (B : LinearMap.BilinForm ℤ M)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) (z : M) :
    remainderMap B h z = Lattice.orthogonalRemainder B d x y z := rfl

def remainderInComplement (B : LinearMap.BilinForm ℤ M) (hB : B.IsAlt)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) : M →ₗ[ℤ] complement B x y :=
  (remainderMap B h).codRestrict (complement B x y) (Lattice.remainder_orthogonal B hB h)

theorem coordinate_values (B : LinearMap.BilinForm ℤ M) (hB : B.IsAlt)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) :
    firstCoordinate B h x = 1 ∧ firstCoordinate B h y = 0 ∧
      secondCoordinate B h x = 0 ∧ secondCoordinate B h y = 1 := by
  change B x y / d = 1 ∧ B y y / d = 0 ∧ B x x / d = 0 ∧ B x y / d = 1
  simp only [h.2.1, hB x, hB y, Int.ediv_self h.1.ne', Int.zero_ediv, and_self]

theorem coordinates_complement (B : LinearMap.BilinForm ℤ M)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) (z : complement B x y) :
    firstCoordinate B h z.val = 0 ∧ secondCoordinate B h z.val = 0 := by
  change B z.val y / d = 0 ∧ B x z.val / d = 0
  have hz : B x z.val = 0 ∧ B z.val y = 0 := z.property
  rw [hz.1, hz.2, Int.zero_ediv]
  exact ⟨rfl, rfl⟩

theorem remainder_values (B : LinearMap.BilinForm ℤ M) (hB : B.IsAlt)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) :
    remainderMap B h x = 0 ∧ remainderMap B h y = 0 ∧
      ∀ z : complement B x y, remainderMap B h z.val = z.val := by
  obtain ⟨h1x, h1y, h2x, h2y⟩ := coordinate_values B hB h
  refine ⟨?_, ?_, ?_⟩
  · change x - firstCoordinate B h x • x - secondCoordinate B h x • y = 0
    rw [h1x, h2x, one_smul, zero_smul, sub_self, sub_zero]
  · change y - firstCoordinate B h y • x - secondCoordinate B h y • y = 0
    rw [h1y, h2y, one_smul, zero_smul, sub_zero, sub_self]
  · intro z
    obtain ⟨h1, h2⟩ := coordinates_complement B h z
    change z.val - firstCoordinate B h z.val • x - secondCoordinate B h z.val • y = z.val
    rw [h1, h2, zero_smul, zero_smul, sub_zero, sub_zero]

def splittingMap (B : LinearMap.BilinForm ℤ M) (hB : B.IsAlt)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) :
    M →ₗ[ℤ] (ℤ × ℤ) × complement B x y :=
  ((firstCoordinate B h).prod (secondCoordinate B h)).prod (remainderInComplement B hB h)

def reconstruct (x y : M) {S : Submodule ℤ M} (z : (ℤ × ℤ) × S) : M :=
  z.1.1 • x + z.1.2 • y + z.2.val

theorem reconstruct_splitting (B : LinearMap.BilinForm ℤ M) (hB : B.IsAlt)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) (z : M) :
    reconstruct x y (splittingMap B hB h z) = z := by
  change firstCoordinate B h z • x + secondCoordinate B h z • y +
    (z - firstCoordinate B h z • x - secondCoordinate B h z • y) = z
  abel

theorem splitting_reconstruct (B : LinearMap.BilinForm ℤ M) (hB : B.IsAlt)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y)
    (z : (ℤ × ℤ) × complement B x y) :
    splittingMap B hB h (reconstruct x y z) = z := by
  obtain ⟨h1x, h1y, h2x, h2y⟩ := coordinate_values B hB h
  obtain ⟨h1z, h2z⟩ := coordinates_complement B h z.2
  obtain ⟨hRx, hRy, hRz⟩ := remainder_values B hB h
  apply Prod.ext
  · apply Prod.ext
    · change firstCoordinate B h (z.1.1 • x + z.1.2 • y + z.2.val) = z.1.1
      simp only [map_add, map_zsmul, h1x, h1y, h1z, smul_eq_mul, mul_one, mul_zero, add_zero]
    · change secondCoordinate B h (z.1.1 • x + z.1.2 • y + z.2.val) = z.1.2
      simp only [map_add, map_zsmul, h2x, h2y, h2z, smul_eq_mul, mul_one, mul_zero,
        zero_add, add_zero]
  · apply Subtype.ext
    change remainderMap B h (z.1.1 • x + z.1.2 • y + z.2.val) = z.2.val
    simp only [map_add, map_zsmul, hRx, hRy, hRz, smul_zero, zero_add]

/-- An actual integral orthogonal splitting; no rational division of
lattice vectors occurs because the coordinate pairings are divisible by d. -/
def splitPair (B : LinearMap.BilinForm ℤ M) (hB : B.IsAlt)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) :
    M ≃ₗ[ℤ] (ℤ × ℤ) × complement B x y :=
  LinearEquiv.ofBijective (splittingMap B hB h)
    ⟨Function.LeftInverse.injective (reconstruct_splitting B hB h),
      Function.RightInverse.surjective (splitting_reconstruct B hB h)⟩

theorem complement_nondegenerate (B : LinearMap.BilinForm ℤ M) (hB : B.IsAlt)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) :
    ∀ z : complement B x y, (∀ w : complement B x y, B z.val w.val = 0) → z = 0 := by
  intro z hz
  apply Subtype.ext
  apply hnd z.val
  intro w
  have hzxy : B x z.val = 0 ∧ B z.val y = 0 := z.property
  have hzx : B z.val x = 0 := by rw [← hB.neg_eq, hzxy.1, neg_zero]
  have hdecomp := reconstruct_splitting B hB h w
  rw [← hdecomp]
  change B z.val (firstCoordinate B h w • x + secondCoordinate B h w • y +
    (remainderInComplement B hB h w).val) = 0
  simp only [map_add, map_zsmul, hzx, hzxy.2, hz, smul_zero, add_zero]

theorem pairing_split (B : LinearMap.BilinForm ℤ M) (hB : B.IsAlt)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y) (z w : M) :
    B z w = d * (firstCoordinate B h z * secondCoordinate B h w -
      firstCoordinate B h w * secondCoordinate B h z) +
      B (remainderInComplement B hB h z).val (remainderInComplement B hB h w).val := by
  let rz := remainderInComplement B hB h z
  let rw' := remainderInComplement B hB h w
  have hz : B x rz.val = 0 ∧ B rz.val y = 0 := rz.property
  have hw : B x rw'.val = 0 ∧ B rw'.val y = 0 := rw'.property
  have hzx : B rz.val x = 0 := by rw [← hB.neg_eq, hz.1, neg_zero]
  have hyw : B y rw'.val = 0 := by rw [← hB.neg_eq, hw.2, neg_zero]
  calc
    B z w = B (firstCoordinate B h z • x + secondCoordinate B h z • y + rz.val)
        (firstCoordinate B h w • x + secondCoordinate B h w • y + rw'.val) :=
      congrArg₂ (fun a b => B a b) (reconstruct_splitting B hB h z).symm
        (reconstruct_splitting B hB h w).symm
    _ = _ := by
      simp only [map_add, LinearMap.add_apply, map_zsmul, LinearMap.smul_apply,
        hz.2, hw.1, hzx, hyw, hB x, hB y, h.2.1, ← hB.neg_eq x y,
        smul_eq_mul, mul_zero, add_zero, zero_add]
      ring

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.Split

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.NormalForm

/-! Integral paired coordinates for a nondegenerate alternating lattice.
The elementary divisors and their divisibility order are constructed by
induction, splitting off a least positive pairing at each step. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.Lattice OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.Split

abbrev Coordinates (k : ℕ) := Fin k → ℤ × ℤ

def weightedPairing {k : ℕ} (d : Fin k → ℤ) (z w : Coordinates k) : ℤ :=
  ∑ i, d i * ((z i).1 * (w i).2 - (w i).1 * (z i).2)

structure NormalCoordinates {M : Type*} [AddCommGroup M]
    (B : LinearMap.BilinForm ℤ M) where
  count : ℕ
  coefficient : Fin count → ℤ
  positive : ∀ i, 0 < coefficient i
  chain : ∀ i j, i ≤ j → coefficient i ∣ coefficient j
  equiv : M ≃ₗ[ℤ] Coordinates count
  pairing : ∀ z w, B z w = weightedPairing coefficient (equiv z) (equiv w)

theorem weightedPairing_axes {k : ℕ} (d : Fin k → ℤ) (i : Fin k) :
    weightedPairing d (Pi.single i (1, 0)) (Pi.single i (0, 1)) = d i := by
  unfold weightedPairing
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp only [Pi.single_eq_of_ne hji, Prod.fst_zero, Prod.snd_zero,
      mul_zero, sub_self]
  · simp

theorem coefficient_is_pairing {M : Type*} [AddCommGroup M]
    {B : LinearMap.BilinForm ℤ M} (C : NormalCoordinates B) (i : Fin C.count) :
    ∃ x y : M, B x y = C.coefficient i := by
  refine ⟨C.equiv.symm (Pi.single i (1, 0)), C.equiv.symm (Pi.single i (0, 1)), ?_⟩
  rw [C.pairing, C.equiv.apply_symm_apply, C.equiv.apply_symm_apply, weightedPairing_axes]

def complementForm {M : Type*} [AddCommGroup M]
    (B : LinearMap.BilinForm ℤ M) (x y : M) :
    LinearMap.BilinForm ℤ (Split.complement B x y) :=
  B.compl₁₂ (Split.complement B x y).subtype (Split.complement B x y).subtype

def prependCoordinates {M : Type*} [AddCommGroup M]
    (B : LinearMap.BilinForm ℤ M) (hB : B.IsAlt)
    {d : ℤ} {x y : M} (h : Lattice.IsMinimalPair B d x y)
    (C : NormalCoordinates (complementForm B x y)) : NormalCoordinates B := by
  let e := (Split.splitPair B hB h).trans
    ((LinearEquiv.prodCongr (LinearEquiv.refl ℤ (ℤ × ℤ)) C.equiv).trans
      (Fin.consLinearEquiv ℤ (fun _ : Fin (C.count + 1) => ℤ × ℤ)))
  have hd : ∀ i, d ∣ C.coefficient i := by
    intro i
    obtain ⟨z, w, hzw⟩ := coefficient_is_pairing C i
    rw [← hzw]
    exact Lattice.minimal_pair_dvd_all B hB h z.val w.val
  refine {
    count := C.count + 1
    coefficient := Fin.cons d C.coefficient
    positive := ?_
    chain := ?_
    equiv := e
    pairing := ?_ }
  · intro i
    refine Fin.cases h.1 (fun j => C.positive j) i
  · intro i j
    induction i using Fin.cases with
    | zero =>
        intro _
        exact Fin.cases (dvd_refl d) (fun b => hd b) j
    | succ a =>
        induction j using Fin.cases with
        | zero => intro hbad; simp at hbad
        | succ b => intro hij; exact C.chain a b (Fin.succ_le_succ_iff.mp hij)
  · intro z w
    have hpair := Split.pairing_split B hB h z w
    change B z w = weightedPairing (Fin.cons d C.coefficient)
      (Fin.cons (Split.firstCoordinate B h z, Split.secondCoordinate B h z)
        (C.equiv (Split.remainderInComplement B hB h z)))
      (Fin.cons (Split.firstCoordinate B h w, Split.secondCoordinate B h w)
        (C.equiv (Split.remainderInComplement B hB h w)))
    rw [weightedPairing, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    change B z w = _ + weightedPairing C.coefficient
      (C.equiv (Split.remainderInComplement B hB h z)) (C.equiv (Split.remainderInComplement B hB h w))
    rw [← C.pairing]
    exact hpair

/-- Construct the ordered paired normal form, rather than taking a
polarization type as an extra input. -/
theorem exists_normal_coordinates :
    ∀ (n : ℕ) (M : Type*) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M],
      Module.finrank ℤ M = n → ∀ B : LinearMap.BilinForm ℤ M,
        B.IsAlt → (∀ x, (∀ y, B x y = 0) → x = 0) → Nonempty (NormalCoordinates B) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M _ _ _ hdim B hB hnd
    by_cases hn : n = 0
    · let : Subsingleton M := (Module.finrank_eq_zero_iff_of_free ℤ M).mp (hdim.trans hn)
      let e : M ≃ₗ[ℤ] Coordinates 0 := LinearEquiv.ofBijective 0
        ⟨fun _ _ _ => Subsingleton.elim _ _, fun z => ⟨0, Subsingleton.elim _ z⟩⟩
      refine ⟨⟨0, Fin.elim0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), e, ?_⟩⟩
      intro z w
      have hz : z = 0 := Subsingleton.elim _ _
      simp only [hz, map_zero, LinearMap.zero_apply, weightedPairing, Finset.univ_eq_empty,
        Finset.sum_empty]
    · have hp : 0 < Module.finrank ℤ M := by omega
      let : Nontrivial M := (Module.finrank_pos_iff_of_free ℤ M).mp hp
      have hex : ∃ x y : M, B x y ≠ 0 := by
        obtain ⟨x, hx⟩ := exists_ne (0 : M)
        by_contra hzero
        push Not at hzero
        exact hx (hnd x (hzero x))
      obtain ⟨d, x, y, hpair⟩ := Lattice.exists_minimal_pair B hex
      let S := Split.complement B x y
      let BS := complementForm B x y
      have hSdim : Module.finrank ℤ S < n := by
        have heq := (Split.splitPair B hB hpair).finrank_eq
        simp only [Module.finrank_prod, Module.finrank_self] at heq
        change Module.finrank ℤ M = 1 + 1 + Module.finrank ℤ S at heq
        omega
      have hBS : BS.IsAlt := fun z => hB z.val
      have hBSnd : ∀ z : S, (∀ w : S, BS z w = 0) → z = 0 :=
        Split.complement_nondegenerate B hB hnd hpair
      obtain ⟨C⟩ := ih (Module.finrank ℤ S) hSdim S rfl BS hBS hBSnd
      exact ⟨prependCoordinates B hB hpair C⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.NormalForm

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.PolarizationType

/-! Identify the cokernel of the actual integral alternating form from
its constructed paired coordinates. This supplies ReferenceFamily's doubled
elementary-divisor convention. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.NormalForm

variable {M : Type*} [AddCommGroup M]
  {B : LinearMap.BilinForm ℤ M} (C : NormalForm.NormalCoordinates B)

def axisX (i : Fin C.count) : M := C.equiv.symm (Pi.single i (1, 0))
def axisY (i : Fin C.count) : M := C.equiv.symm (Pi.single i (0, 1))

theorem coordinate_decomposition (z : M) :
    z = ∑ i, ((C.equiv z i).1 • axisX C i + (C.equiv z i).2 • axisY C i) := by
  apply C.equiv.injective
  simp only [map_sum, map_add, map_zsmul, axisX, axisY, C.equiv.apply_symm_apply]
  funext j
  rw [Finset.sum_apply]
  symm
  rw [Finset.sum_eq_single j]
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
    apply Prod.ext <;> simp
  · intro i _ hij
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hij),
      smul_zero, add_zero]
  · simp

theorem dual_ext (f g : M →ₗ[ℤ] ℤ)
    (hx : ∀ i, f (axisX C i) = g (axisX C i))
    (hy : ∀ i, f (axisY C i) = g (axisY C i)) : f = g := by
  apply LinearMap.ext
  intro z
  rw [coordinate_decomposition C z]
  simp only [map_sum, map_add, map_zsmul, hx, hy]

def coordinateFunctional (a b : Fin C.count → ℤ) : M →ₗ[ℤ] ℤ :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun z => ∑ i, (a i * (C.equiv z i).1 + b i * (C.equiv z i).2)
    map_zero' := by simp
    map_add' := by
      intro z w
      simp only [map_add, Pi.add_apply, Prod.fst_add, Prod.snd_add, mul_add]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring }

theorem coordinateFunctional_axes (a b : Fin C.count → ℤ) (i : Fin C.count) :
    coordinateFunctional C a b (axisX C i) = a i ∧
      coordinateFunctional C a b (axisY C i) = b i := by
  simp [coordinateFunctional, axisX, axisY, Pi.single_apply, apply_ite]

theorem pairing_axes (z : M) (i : Fin C.count) :
    B z (axisX C i) = -(C.coefficient i * (C.equiv z i).2) ∧
      B z (axisY C i) = C.coefficient i * (C.equiv z i).1 := by
  constructor <;> rw [C.pairing]
  · simp [NormalForm.weightedPairing, axisX, Pi.single_apply, apply_ite]
  · simp [NormalForm.weightedPairing, axisY, Pi.single_apply, apply_ite]

abbrev finiteType :=
  (∀ i : Fin C.count, ZMod (C.coefficient i).natAbs) ×
    (∀ i : Fin C.count, ZMod (C.coefficient i).natAbs)

def reduction : (M →ₗ[ℤ] ℤ) →ₗ[ℤ] finiteType C :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun f => (fun i => (f (axisX C i) : ZMod (C.coefficient i).natAbs),
      fun i => (f (axisY C i) : ZMod (C.coefficient i).natAbs))
    map_zero' := by ext i <;> simp
    map_add' := by intro f g; ext i <;> simp }

theorem reduction_surjective : Function.Surjective (reduction C) := by
  intro z
  choose a ha using fun i => ZMod.intCast_surjective (z.1 i)
  choose b hb using fun i => ZMod.intCast_surjective (z.2 i)
  refine ⟨coordinateFunctional C a b, ?_⟩
  apply Prod.ext
  · funext i
    change (coordinateFunctional C a b (axisX C i) : ZMod (C.coefficient i).natAbs) = z.1 i
    rw [(coordinateFunctional_axes C a b i).1]
    exact ha i
  · funext i
    change (coordinateFunctional C a b (axisY C i) : ZMod (C.coefficient i).natAbs) = z.2 i
    rw [(coordinateFunctional_axes C a b i).2]
    exact hb i

theorem reduction_ker : LinearMap.ker (reduction C) = LinearMap.range B := by
  apply le_antisymm
  · intro f hf
    have hdivX : ∀ i, C.coefficient i ∣ f (axisX C i) := by
      intro i
      have heq := congrArg (fun z : finiteType C => z.1 i) hf
      change (f (axisX C i) : ZMod (C.coefficient i).natAbs) = 0 at heq
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp heq
      simpa only [Int.natCast_natAbs, abs_of_pos (C.positive i)] using hd
    have hdivY : ∀ i, C.coefficient i ∣ f (axisY C i) := by
      intro i
      have heq := congrArg (fun z : finiteType C => z.2 i) hf
      change (f (axisY C i) : ZMod (C.coefficient i).natAbs) = 0 at heq
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp heq
      simpa only [Int.natCast_natAbs, abs_of_pos (C.positive i)] using hd
    let z := C.equiv.symm (fun i =>
      (f (axisY C i) / C.coefficient i, -(f (axisX C i) / C.coefficient i)))
    refine ⟨z, dual_ext C (B z) f ?_ ?_⟩
    · intro i
      rw [(pairing_axes C z i).1]
      simp only [z, C.equiv.apply_symm_apply]
      rw [mul_neg, neg_neg, mul_comm, Int.ediv_mul_cancel (hdivX i)]
    · intro i
      rw [(pairing_axes C z i).2]
      simp only [z, C.equiv.apply_symm_apply]
      rw [mul_comm, Int.ediv_mul_cancel (hdivY i)]
  · rintro _ ⟨z, rfl⟩
    apply Prod.ext
    · funext i
      change (B z (axisX C i) : ZMod (C.coefficient i).natAbs) = 0
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      rw [Int.natCast_natAbs, abs_of_pos (C.positive i), (pairing_axes C z i).1]
      exact dvd_neg.mpr (dvd_mul_right _ _)
    · funext i
      change (B z (axisY C i) : ZMod (C.coefficient i).natAbs) = 0
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      rw [Int.natCast_natAbs, abs_of_pos (C.positive i), (pairing_axes C z i).2]
      exact dvd_mul_right _ _

/-- The finite cokernel is the doubled product of the constructed cyclic
elementary divisors, exactly as required by the reference PEL datum. -/
def cokernelEquiv : ((M →ₗ[ℤ] ℤ) ⧸ LinearMap.range B) ≃+ finiteType C :=
  ((Submodule.quotEquivOfEq _ _ (reduction_ker C).symm).trans
    (LinearMap.quotKerEquivOfSurjective (reduction C) (reduction_surjective C))).toAddEquiv

theorem polarization_type_exists [Module.Free ℤ M] [Module.Finite ℤ M]
    (hB : B.IsAlt) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ (k : ℕ) (d : Fin k → ℕ),
      Module.finrank ℤ M = 2 * k ∧
      (∀ i, 0 < d i) ∧ (∀ i j, i ≤ j → d i ∣ d j) ∧
      Nonempty (((M →ₗ[ℤ] ℤ) ⧸ LinearMap.range B) ≃+
        ((∀ i : Fin k, ZMod (d i)) × (∀ i : Fin k, ZMod (d i)))) := by
  obtain ⟨C⟩ := NormalForm.exists_normal_coordinates (Module.finrank ℤ M) M rfl B hB hnd
  refine ⟨C.count, fun i => (C.coefficient i).natAbs, ?_, ?_, ?_, ⟨cokernelEquiv C⟩⟩
  · have heq := C.equiv.finrank_eq
    simpa only [NormalForm.Coordinates, Module.finrank_pi_fintype, Module.finrank_prod, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm] using heq
  · intro i
    exact Int.natAbs_pos.mpr (C.positive i).ne'
  · intro i j hij
    exact Int.natAbs_dvd_natAbs.mpr (C.chain i j hij)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlternatingPolarization.CM.PolarizationType

end

end OAI
