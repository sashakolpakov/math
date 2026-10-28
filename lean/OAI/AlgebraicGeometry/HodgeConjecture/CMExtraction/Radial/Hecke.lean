import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity
import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Hecke -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Hecke

noncomputable section

section

/-! The actual SL3 substitution representation and its finite spherical
coset sum commute with normalized scalar dilation on functions. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]

def matrixSubstitution : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q →*
    ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ) ≃ₗ[ℂ] (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ)) where
  toFun g := RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator
    (Matrix.SpecialLinearGroup.toGL g)
  map_one' := by
    ext f x
    change f ((↑((Matrix.SpecialLinearGroup.toGL (1 : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q))⁻¹) :
      Matrix (Fin 3) (Fin 3) ℚ_[q]).mulVec x) = f x
    simp only [map_one, inv_one, Units.val_one, Matrix.one_mulVec]
  map_mul' g h := by
    ext f x
    change f ((↑((Matrix.SpecialLinearGroup.toGL (g * h))⁻¹) :
      Matrix (Fin 3) (Fin 3) ℚ_[q]).mulVec x) =
      f ((↑((Matrix.SpecialLinearGroup.toGL h)⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q]).mulVec
        ((↑((Matrix.SpecialLinearGroup.toGL g)⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q]).mulVec x))
    simp only [map_mul, mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

def functionDilation : (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ) →ₗ[ℂ] (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ) :=
  Cyclicity.normalization q • RepresentationTheory.Hecke.RadialDilation.Mem.Realization.inverseSubstitution q (q : ℚ_[q])

theorem functionDilation_radial (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    functionDilation q b.val = (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q b).val := rfl

theorem matrixSubstitution_dilation (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (f : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ) :
    matrixSubstitution q g (functionDilation q f) =
      functionDilation q (matrixSubstitution q g f) := by
  funext x
  change Cyclicity.normalization q * f (fun i => (q : ℚ_[q])⁻¹ *
      ((↑((Matrix.SpecialLinearGroup.toGL g)⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q]).mulVec x) i) =
    Cyclicity.normalization q * f
      ((↑((Matrix.SpecialLinearGroup.toGL g)⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q]).mulVec
        (fun i => (q : ℚ_[q])⁻¹ * x i))
  congr 2
  exact (Matrix.mulVec_smul
    (↑((Matrix.SpecialLinearGroup.toGL g)⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q])
    (q : ℚ_[q])⁻¹ x).symm

def sphericalFunctionAction (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ) →ₗ[ℂ] (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ) :=
  RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (matrixSubstitution q) T

theorem sphericalFunctionAction_dilation (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (f : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ) :
    sphericalFunctionAction q T (functionDilation q f) =
      functionDilation q (sphericalFunctionAction q T f) := by
  change (((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).sum fun c a =>
      (a : ℂ) • (matrixSubstitution q c.out).toLinearMap) (functionDilation q f)) = _
  simp only [sphericalFunctionAction, RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator, LinearMap.finsupp_sum_apply]
  simp only [Finsupp.sum, map_sum, LinearMap.smul_apply, map_smul,
    LinearEquiv.coe_coe, matrixSubstitution_dilation]

end

section

/-! Ball indicators, and hence all radial inputs, are fixed by the
actual integral special-linear group. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]

theorem integral_entry_bound (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q)
    (hg : g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (i j : Fin 3) : ‖g.val i j‖ ≤ 1 := by
  obtain ⟨G, rfl⟩ := hg
  exact (G.val i j).property

theorem integral_mulVec_bound (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q)
    (hg : g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (R : ℝ) (hR : 0 ≤ R)
    (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) (hx : ∀ i, ‖x i‖ ≤ R) : ∀ i, ‖g.val.mulVec x i‖ ≤ R := by
  intro i
  change ‖∑ j : Fin 3, g.val i j * x j‖ ≤ R
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR
  intro j _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (integral_entry_bound q g hg i j)).trans (hx j)

theorem integral_inverse_ball_iff (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q)
    (hg : g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (R : ℝ) (hR : 0 ≤ R) (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) :
    (∀ i, ‖(g⁻¹).val.mulVec x i‖ ≤ R) ↔ ∀ i, ‖x i‖ ≤ R := by
  constructor
  · intro hx
    have h := integral_mulVec_bound q g hg R hR ((g⁻¹).val.mulVec x) hx
    have hc : g.val.mulVec ((g⁻¹).val.mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    simpa only [hc] using h
  · exact integral_mulVec_bound q g⁻¹ ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).inv_mem hg) R hR x

theorem integral_substitution_ball (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q)
    (hg : g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (n : ℤ) :
    matrixSubstitution q g (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q n) = RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q n := by
  funext x
  have hq : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  change RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q n
    ((↑((Matrix.SpecialLinearGroup.toGL g)⁻¹) : Matrix (Fin 3) (Fin 3) ℚ_[q]).mulVec x) = _
  rw [← map_inv]
  change (if ∀ i, ‖(g⁻¹).val.mulVec x i‖ ≤ (q : ℝ) ^ (-n) then (1 : ℂ) else 0) = _
  simp only [integral_inverse_ball_iff q g hg _ (zpow_pos hq _).le, RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall]

theorem radial_integral_fixed (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    b.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (matrixSubstitution q) := by
  apply (show RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q ≤ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
    (matrixSubstitution q) from ?_) b.property
  apply Submodule.span_le.mpr
  rintro f ⟨n, rfl⟩ g hg
  exact integral_substitution_ball q g hg n

def radialFixedEmbedding : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ]
    RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (matrixSubstitution q) :=
  (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q).inclusion (fun b hb => radial_integral_fixed q ⟨b, hb⟩)

theorem spherical_radial_integral_fixed (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    sphericalFunctionAction q T b.val ∈
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (matrixSubstitution q) :=
  RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.weilOperator_preserves_fixed (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (matrixSubstitution q) T
    (radialFixedEmbedding q b)

end

section

/-! Integral special-linear matrices act transitively on each nonzero
sup-norm sphere. The matrices come from explicit primitive columns. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]

theorem primitive_column (v : Fin 3 → ℤ_[q]) (hv : ∃ i, IsUnit (v i)) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) ℤ_[q], ∀ i, g.val i 0 = v i := by
  obtain ⟨k, u, hu⟩ := hv
  fin_cases k
  · refine ⟨⟨!![v 0, 0, 0; v 1, (↑u⁻¹ : ℤ_[q]), 0; v 2, 0, 1], ?_⟩, ?_⟩
    · simpa [Matrix.det_fin_three] using hu.symm
    · intro i; fin_cases i <;> rfl
  · refine ⟨⟨!![v 0, -(↑u⁻¹ : ℤ_[q]), 0; v 1, 0, 0; v 2, 0, 1], ?_⟩, ?_⟩
    · simpa [Matrix.det_fin_three] using hu
    · intro i; fin_cases i <;> rfl
  · refine ⟨⟨!![v 0, 0, -(↑u⁻¹ : ℤ_[q]); v 1, 1, 0; v 2, 0, 0], ?_⟩, ?_⟩
    · simpa [Matrix.det_fin_three] using hu
    · intro i; fin_cases i <;> rfl

theorem exists_max_coordinate (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) (hx : x ≠ 0) :
    ∃ k : Fin 3, x k ≠ 0 ∧ ∀ i, ‖x i‖ ≤ ‖x k‖ := by
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 3 => ‖x i‖) Finset.univ_nonempty
  refine ⟨k, ?_, fun i => hk i (Finset.mem_univ i)⟩
  intro hz
  apply hx
  funext i
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hz, norm_zero] using hk i (Finset.mem_univ i)

theorem integral_column_from_scalar (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) (a : ℚ_[q]) (ha : a ≠ 0)
    (hbound : ∀ i, ‖x i‖ ≤ ‖a‖) (heq : ∃ i, ‖x i‖ = ‖a‖) :
    ∃ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q ∧
      ∀ i, g.val i 0 * a = x i := by
  let v : Fin 3 → ℤ_[q] := fun i => ⟨x i / a, by
    rw [norm_div]
    exact (div_le_one₀ (norm_pos_iff.mpr ha)).mpr (hbound i)⟩
  obtain ⟨k, hk⟩ := heq
  have hv : IsUnit (v k) := PadicInt.isUnit_iff.mpr (by
    change ‖x k / a‖ = 1
    rw [norm_div, hk, div_self (norm_ne_zero_iff.mpr ha)])
  obtain ⟨G, hG⟩ := primitive_column q v ⟨k, hv⟩
  let g := Matrix.SpecialLinearGroup.map (PadicInt.Coe.ringHom (p := q)) G
  refine ⟨g, ⟨G, rfl⟩, ?_⟩
  intro i
  change (↑(G.val i 0) : ℚ_[q]) * a = x i
  rw [hG]
  exact div_mul_cancel₀ _ ha

theorem max_coordinate_norm (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) (k : Fin 3)
    (hk : ∀ i, ‖x i‖ ≤ ‖x k‖) : ‖x k‖ = ‖x‖ := by
  apply le_antisymm (norm_le_pi_norm x k)
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr hk

theorem integral_transitive_on_sphere (x y : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) (hxy : ‖x‖ = ‖y‖) :
    ∃ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, g ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q ∧ g.val.mulVec x = y := by
  by_cases hx : x = 0
  · have hy : y = 0 := norm_eq_zero.mp (by rw [← hxy, hx, norm_zero])
    exact ⟨1, (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).one_mem, by simp [hx, hy]⟩
  have hy : y ≠ 0 := by
    intro hy
    apply hx
    exact norm_eq_zero.mp (by rw [hxy, hy, norm_zero])
  obtain ⟨k, hk, hmax⟩ := exists_max_coordinate q x hx
  obtain ⟨l, _, hlmax⟩ := exists_max_coordinate q y hy
  have hn : ‖y l‖ = ‖x k‖ :=
    (max_coordinate_norm q y l hlmax).trans (hxy.symm.trans (max_coordinate_norm q x k hmax).symm)
  obtain ⟨gx, hgx, hxg⟩ := integral_column_from_scalar q x (x k) hk hmax ⟨k, rfl⟩
  obtain ⟨gy, hgy, hyg⟩ := integral_column_from_scalar q y (x k) hk
    (fun i => (hlmax i).trans hn.le) ⟨l, hn⟩
  have hx' : gx.val.mulVec (Pi.single 0 (x k)) = x := by
    funext i
    rw [Matrix.mulVec_single]
    exact hxg i
  have hy' : gy.val.mulVec (Pi.single 0 (x k)) = y := by
    funext i
    rw [Matrix.mulVec_single]
    exact hyg i
  refine ⟨gy * gx⁻¹, (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).mul_mem hgy
    ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).inv_mem hgx), ?_⟩
  rw [← hx', Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_assoc, inv_mul_cancel, mul_one, hy']

theorem integral_fixed_eq_of_norm_eq
    (f : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (matrixSubstitution q))
    (x y : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) (hxy : ‖x‖ = ‖y‖) : f.val x = f.val y := by
  obtain ⟨g, hg, hgy⟩ := integral_transitive_on_sphere q x y hxy
  have h := congrArg (fun f : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ => f x)
    (f.property g⁻¹ ((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).inv_mem hg))
  change f.val ((↑((Matrix.SpecialLinearGroup.toGL g⁻¹)⁻¹) :
    Matrix (Fin 3) (Fin 3) ℚ_[q]).mulVec x) = f.val x at h
  rw [map_inv, inv_inv] at h
  exact (hgy ▸ h).symm

end

section

/-! Finite radial bands are linear combinations of the actual ball
indicators. The discrete radius argument uses the p-adic valuation. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]

def radius (n : ℤ) : ℝ := (q : ℝ) ^ (-n)

theorem radius_pos (n : ℤ) : 0 < radius q n :=
  zpow_pos (by exact_mod_cast (Fact.out : q.Prime).pos) _

theorem radius_antitone : Antitone (radius q) := by
  intro m n hmn
  apply zpow_le_zpow_right₀
  · exact_mod_cast (Fact.out : q.Prime).one_lt.le
  · omega

theorem ball_norm (n : ℤ) (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) :
    RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q n x = if ‖x‖ ≤ radius q n then (1 : ℂ) else 0 := by
  have h : (∀ i, ‖x i‖ ≤ radius q n) ↔ ‖x‖ ≤ radius q n :=
    (pi_norm_le_iff_of_nonneg (radius_pos q n).le).symm
  change (if ∀ i, ‖x i‖ ≤ radius q n then (1 : ℂ) else 0) = _
  simp only [h]

theorem ball_zero (n : ℤ) : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q n 0 = 1 := by
  rw [ball_norm, norm_zero, ite_eq_left (radius_pos q n).le]

def spherePoint (n : ℤ) : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q := Pi.single 0 ((q : ℚ_[q]) ^ n)

theorem spherePoint_norm (n : ℤ) : ‖spherePoint q n‖ = radius q n := by
  rw [spherePoint, Pi.norm_single, Padic.norm_p_zpow]
  rfl

theorem radius_gap (m : ℤ) (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q)
    (hlo : ‖x‖ ≤ radius q m) (hhi : radius q (m + 1) < ‖x‖) :
    ‖x‖ = radius q m := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at hhi
    exact (not_lt_of_ge (radius_pos q (m + 1)).le) hhi
  obtain ⟨k, _, hk⟩ := exists_max_coordinate q x hx
  have hkn := max_coordinate_norm q x k hk
  apply le_antisymm hlo
  apply le_of_not_gt
  intro hlt
  have h := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one (x k) (-m)).mp
    (hkn ▸ hlt)
  have he : -m - 1 = -(m + 1) := by omega
  rw [he, hkn] at h
  exact (not_le_of_gt hhi) h

theorem radial_mem_of_bands (N : ℕ) (m : ℤ) (f : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ)
    (hnorm : ∀ x y, ‖x‖ = ‖y‖ → f x = f y)
    (hout : ∀ x, radius q m < ‖x‖ → f x = 0)
    (hin : ∀ x, ‖x‖ ≤ radius q (m + N) → f x = f 0) :
    f ∈ RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q := by
  induction N generalizing m f with
  | zero =>
      have he : f = f 0 • RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q m := by
        funext x
        rw [Pi.smul_apply, smul_eq_mul, ball_norm]
        split_ifs with hx
        · rw [mul_one]
          exact hin x (by simpa using hx)
        · rw [mul_zero]
          exact hout x (lt_of_not_ge hx)
      rw [he]
      exact (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q).smul_mem _ (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall_mem q m)
  | succ N ih =>
      let c := f (spherePoint q m)
      let w : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ := c • (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q m - RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q (m + 1))
      let g := f - w
      have hw : w ∈ RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q := (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q).smul_mem c
        ((RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q).sub_mem (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall_mem q m) (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall_mem q (m + 1)))
      have hwzero : w 0 = 0 := by simp [w, ball_zero]
      have hwinner (x : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q) (hx : ‖x‖ ≤ radius q (m + 1)) : w x = 0 := by
        have hx' := hx.trans (radius_antitone q (by omega : m ≤ m + 1))
        simp only [w, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ball_norm,
          ite_eq_left hx, ite_eq_left hx', sub_self, mul_zero]
      have hgnorm : ∀ x y, ‖x‖ = ‖y‖ → g x = g y := by
        intro x y hxy
        simp only [g, Pi.sub_apply, w, Pi.smul_apply, smul_eq_mul, ball_norm,
          hnorm x y hxy, hxy]
      have hgout : ∀ x, radius q (m + 1) < ‖x‖ → g x = 0 := by
        intro x hx
        by_cases ho : radius q m < ‖x‖
        · simp only [g, Pi.sub_apply, hout x ho, w, Pi.smul_apply, smul_eq_mul,
            ball_norm, ite_eq_right (not_le_of_gt ho), ite_eq_right (not_le_of_gt hx),
            sub_self, mul_zero]
        · have hn := radius_gap q m x (le_of_not_gt ho) hx
          have hf : f x = c := hnorm x (spherePoint q m) (hn.trans (spherePoint_norm q m).symm)
          simp only [g, Pi.sub_apply, hf, w, Pi.smul_apply, smul_eq_mul,
            ball_norm, ite_eq_left (le_of_not_gt ho), ite_eq_right (not_le_of_gt hx),
            sub_zero, mul_one, sub_self]
      have hgin : ∀ x, ‖x‖ ≤ radius q (m + 1 + N) → g x = g 0 := by
        intro x hx
        have hi : ‖x‖ ≤ radius q (m + (N + 1 : ℕ)) := by
          convert hx using 1
          congr 1
          omega
        have hsmall := hx.trans (radius_antitone q (by omega : m + 1 ≤ m + 1 + (N : ℤ)))
        simp only [g, Pi.sub_apply, hin x hi, hwinner x hsmall, hwzero, sub_zero]
      have hg := ih (m + 1) g hgnorm hgout hgin
      have he : f = g + w := by simp [g]
      rw [he]
      exact (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q).add_mem hg hw

end

/-! Actual ball indicators form a basis of the radial space. Differences
of evaluation on adjacent norm spheres recover their coefficients. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]

theorem radius_le_iff (m n : ℤ) : radius q m ≤ radius q n ↔ n ≤ m := by
  have hq : 1 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  change (q : ℝ) ^ (-m) ≤ (q : ℝ) ^ (-n) ↔ _
  rw [zpow_le_zpow_iff_right₀ hq]
  omega

theorem ball_spherePoint (m n : ℤ) :
    RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q m (spherePoint q n) = if m ≤ n then (1 : ℂ) else 0 := by
  rw [ball_norm, spherePoint_norm]
  simp only [radius_le_iff]

def shellCoefficient (n : ℤ) : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] ℂ where
  toFun b := b.val (spherePoint q n) - b.val (spherePoint q (n - 1))
  map_add' b c := by
    change b.val (spherePoint q n) + c.val (spherePoint q n) -
      (b.val (spherePoint q (n - 1)) + c.val (spherePoint q (n - 1))) = _
    ring
  map_smul' c b := by change c * _ - c * _ = c * (_ - _); ring

theorem shellCoefficient_ball (n m : ℤ) :
    shellCoefficient q n (Cyclicity.ball q m) = if n = m then (1 : ℂ) else 0 := by
  change RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q m (spherePoint q n) - RepresentationTheory.Hecke.RadialDilation.Mem.Realization.radialBall q m (spherePoint q (n - 1)) = _
  rw [ball_spherePoint, ball_spherePoint]
  split_ifs <;> first | omega | norm_num

theorem radial_ball_linearIndependent : LinearIndependent ℂ (Cyclicity.ball q) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one (Cyclicity.ball q) (shellCoefficient q)
  · intro i j hij
    rw [shellCoefficient_ball, ite_eq_right hij]
  · intro i
    rw [shellCoefficient_ball, ite_eq_left rfl]

theorem radial_ball_span : Submodule.span ℂ (Set.range (Cyclicity.ball q)) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (Cyclicity.ball q))
  have h : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q ≤ S.map (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q).subtype := by
    apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    exact ⟨Cyclicity.ball q n, Submodule.subset_span ⟨n, rfl⟩, rfl⟩
  apply top_unique
  intro b _
  obtain ⟨c, hc, he⟩ := h b.property
  exact (Subtype.ext he : c = b) ▸ hc

def radialBasis : Module.Basis ℤ ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :=
  Module.Basis.mk (radial_ball_linearIndependent q) (radial_ball_span q).ge

theorem radialBasis_apply (n : ℤ) : radialBasis q n = Cyclicity.ball q n := Module.Basis.mk_apply _ _ n

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Hecke
