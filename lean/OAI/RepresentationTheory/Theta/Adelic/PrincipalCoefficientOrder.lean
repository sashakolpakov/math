import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # Principal Coefficient Order -/

namespace OAI.RepresentationTheory.Theta.Adelic.PrincipalCoefficientOrder

noncomputable section

/-! Integral coefficient orders and their actual principal ideals.
Clearing the denominator of d makes O_F + N delta O_F a ring, and
N(O_F + delta O_F) an ideal in that ring. -/

open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (d : F)
variable (N : ℕ) (q : 𝓞 F) (hq : (q : F) = (N : F) * d)

def coefficientOrder : Subring (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) where
  carrier := {z | ∃ a b : 𝓞 F, z = ⟨(a : F), (N : F) * (b : F)⟩}
  zero_mem' := ⟨0, 0, by ext <;> simp⟩
  one_mem' := ⟨1, 0, by
    apply QuadraticAlgebra.ext
    · rfl
    · change (0 : F) = (N : F) * 0
      simp⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    refine ⟨a + c, b + e, ?_⟩
    ext <;> simp [mul_add]
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    ext <;> simp
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    refine ⟨a * c + q * N * b * e, a * e + b * c, ?_⟩
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      map_add, map_mul, map_natCast, hq]
    all_goals ring

def coefficientIdeal : Ideal (coefficientOrder F d N q hq) where
  carrier := {z | ∃ a b : 𝓞 F, z.val = ⟨(N : F) * (a : F), (N : F) * (b : F)⟩}
  zero_mem' := ⟨0, 0, by ext <;> simp⟩
  add_mem' := by
    rintro x y ⟨a, b, ha⟩ ⟨c, e, hc⟩
    refine ⟨a + c, b + e, ?_⟩
    change x.val + y.val = _
    rw [ha, hc]
    ext <;> simp [mul_add]
  smul_mem' := by
    rintro x y ⟨c, e, hc⟩
    obtain ⟨a, b, ha⟩ := x.property
    refine ⟨a * c + q * b * e, (N : 𝓞 F) * b * c + a * e, ?_⟩
    change x.val * y.val = _
    rw [ha, hc]
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      map_add, map_mul, map_natCast, hq]
    all_goals ring

omit [NumberField F] in
theorem coefficientIdeal_membership (z : coefficientOrder F d N q hq) :
    z ∈ coefficientIdeal F d N q hq ↔
      ∃ a b : 𝓞 F, z.val = (N : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) * (⟨(a : F), (b : F)⟩ : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) := by
  change (∃ a b : 𝓞 F, z.val = ⟨(N : F) * (a : F), (N : F) * (b : F)⟩) ↔ _
  have hm (a b : 𝓞 F) :
      (N : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) * (⟨(a : F), (b : F)⟩ : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d) =
        ⟨(N : F) * (a : F), (N : F) * (b : F)⟩ := by
    ext <;> simp
  simp only [hm]

end

end OAI.RepresentationTheory.Theta.Adelic.PrincipalCoefficientOrder
