import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Reduction
import OAI.RepresentationTheory.Satake.GL3GL

/-! # Borel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Borel.Iwasawa

noncomputable section

section

/-! The actual upper-triangular subgroup of SL3(Qq) and its diagonal
integer valuations, at the literal integral special-linear level. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]

def upperBorel : Subgroup (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :=
  (RepresentationTheory.Satake.GL3GL.Core.upperBorel ℚ_[q]).comap Matrix.SpecialLinearGroup.toGL

def toGLBorel : upperBorel q →* RepresentationTheory.Satake.GL3GL.Core.upperBorel ℚ_[q] where
  toFun b := ⟨Matrix.SpecialLinearGroup.toGL b.val, b.property⟩
  map_one' := Subtype.ext Matrix.SpecialLinearGroup.toGL.map_one
  map_mul' b c := Subtype.ext (Matrix.SpecialLinearGroup.toGL.map_mul b.val c.val)

def diagonal : upperBorel q →* (Fin 3 → ℚ_[q]ˣ) :=
  (RepresentationTheory.Satake.GL3GL.Core.diagonal ℚ_[q]).comp (toGLBorel q)

theorem diagonal_apply (b : upperBorel q) (i : Fin 3) :
    ((diagonal q b i : ℚ_[q]ˣ) : ℚ_[q]) = b.val.val i i := rfl

def unitValuation : ℚ_[q]ˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (a.val.valuation)
  map_one' := congrArg Multiplicative.ofAdd Padic.valuation_one
  map_mul' a b := congrArg Multiplicative.ofAdd (Padic.valuation_mul a.ne_zero b.ne_zero)

def borelValuation : upperBorel q →* Multiplicative (Fin 3 → ℤ) where
  toFun b := Multiplicative.ofAdd (fun i => (unitValuation q (diagonal q b i)).toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' b c := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrArg Multiplicative.toAdd (by
      change unitValuation q (diagonal q (b * c) i) = _
      rw [map_mul]
      exact (unitValuation q).map_mul _ _)

theorem borelValuation_apply (b : upperBorel q) (i : Fin 3) :
    (borelValuation q b).toAdd i = (b.val.val i i).valuation := rfl

theorem diagonal_product (b : upperBorel q) : ∏ i, diagonal q b i = 1 := by
  apply Units.ext
  change (Units.coeHom ℚ_[q]) (∏ i, diagonal q b i) = (1 : ℚ_[q])
  rw [map_prod]
  change (∏ i, b.val.val i i) = 1
  exact (Matrix.det_of_isUpperTriangular b.property).symm.trans b.val.property

theorem borelValuation_sum (b : upperBorel q) : ∑ i, (borelValuation q b).toAdd i = 0 := by
  have h := congrArg (unitValuation q) (diagonal_product q b)
  rw [map_prod, map_one] at h
  exact congrArg Multiplicative.toAdd h

end

/-! Construct the Iwasawa decomposition at the actual SL3(Zq) level,
with its full torus valuation and sum-zero lattice identity. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]

theorem padic_valuation_zero_of_norm_one (x : ℚ_[q]) (h : ‖x‖ = 1) : x.valuation = 0 := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at h
    exact zero_ne_one h
  have hq : 1 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  apply neg_injective
  apply (zpow_right_strictMono₀ hq).injective
  change (q : ℝ) ^ (-x.valuation) = (q : ℝ) ^ (-(0 : ℤ))
  rw [← Padic.norm_eq_zpow_neg_valuation hx, h, neg_zero, zpow_zero]

theorem compact_borel_valuation (b : upperBorel q) (hb : b.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) :
    borelValuation q b = 1 := by
  obtain ⟨U, hU⟩ := hb
  have htri : U.val.IsUpperTriangular := by
    intro i j hij
    apply Subtype.val_injective
    change (↑(U.val i j) : ℚ_[q]) = 0
    have h : b.val.val i j = 0 := b.property hij
    rw [← hU] at h
    exact h
  have hunit (i : Fin 3) : IsUnit (U.val i i) := by
    have hdet : IsUnit U.val.det := U.property.symm ▸ isUnit_one
    rw [Matrix.det_of_isUpperTriangular htri] at hdet
    exact (IsUnit.prod_univ_iff.mp hdet) i
  apply Multiplicative.toAdd.injective
  funext i
  rw [borelValuation_apply]
  change (b.val.val i i).valuation = 0
  rw [← hU]
  apply padic_valuation_zero_of_norm_one q
  exact PadicInt.isUnit_iff.mp (hunit i)

def decomposition : RepresentationTheory.Satake.GL3TorusIwasawa.Iwasawa.Decomposition (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (Fin 3 → ℤ) where
  B := upperBorel q
  valuation := borelValuation q
  compact_valuation := compact_borel_valuation q
  factorization g := by
    obtain ⟨U, hU⟩ := Reduction.Iwasawa.integralSL3_reduction q g
    let u := Matrix.SpecialLinearGroup.map (PadicInt.Coe.ringHom (p := q)) U
    refine ⟨⟨g * u, hU⟩, ⟨u⁻¹, (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).inv_mem ⟨U, rfl⟩⟩, ?_⟩
    change g = (g * u) * u⁻¹
    rw [mul_assoc, mul_inv_cancel, mul_one]

theorem height_sum (x : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) :
    ∑ i, (decomposition q).height x i = 0 :=
  borelValuation_sum q ((decomposition q).representative x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Borel.Iwasawa
