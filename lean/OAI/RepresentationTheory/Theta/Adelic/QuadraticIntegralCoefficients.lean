import OAI.RepresentationTheory.Weil.AdelicSplitting.Integral

/-! # Quadratic Integral Coefficients -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients

noncomputable section

/-! Coefficient description of the actual order O_v[δ] whenever the
quadratic parameter is integral. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.Integral.Construction

variable {k : Type*} [CommRing k] (S : Subring k) (d : k) (hd : d ∈ S)

def coefficientOrder : Subring (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) where
  carrier := {z | z.re ∈ S ∧ z.im ∈ S}
  zero_mem' := ⟨S.zero_mem, S.zero_mem⟩
  one_mem' := ⟨S.one_mem, S.zero_mem⟩
  add_mem' := by
    rintro x y ⟨hxr, hxi⟩ ⟨hyr, hyi⟩
    exact ⟨S.add_mem hxr hyr, S.add_mem hxi hyi⟩
  neg_mem' := by
    rintro x ⟨hxr, hxi⟩
    exact ⟨S.neg_mem hxr, S.neg_mem hxi⟩
  mul_mem' := by
    rintro x y ⟨hxr, hxi⟩ ⟨hyr, hyi⟩
    constructor
    · change x.re * y.re + d * x.im * y.im ∈ S
      exact S.add_mem (S.mul_mem hxr hyr) (S.mul_mem (S.mul_mem hd hxi) hyi)
    · change x.re * y.im + x.im * y.re + 0 * x.im * y.im ∈ S
      simpa only [zero_mul, add_zero] using S.add_mem (S.mul_mem hxr hyi) (S.mul_mem hxi hyr)

theorem norm_mem (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) (hz : z ∈ coefficientOrder S d hd) :
    QuadraticAlgebra.norm z ∈ S := by
  change z.re * z.re + 0 * z.re * z.im - d * z.im * z.im ∈ S
  simp only [zero_mul, add_zero]
  exact S.sub_mem (S.mul_mem hz.1 hz.1) (S.mul_mem (S.mul_mem hd hz.2) hz.2)

theorem star_mem (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) (hz : z ∈ coefficientOrder S d hd) :
    star z ∈ coefficientOrder S d hd := by
  change (star z).re ∈ S ∧ (star z).im ∈ S
  simpa only [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, zero_mul, add_zero] using
    And.intro hz.1 (S.neg_mem hz.2)

theorem quadraticOrder_coefficients
    (F : Type*) [Field F] [NumberField F] (d : F) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
    (hd : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v) (z : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v) :
    z ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v ↔ z.re ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v ∧ z.im ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v := by
  constructor
  · intro hz
    have hle : Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v ≤ coefficientOrder (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) hd := by
      apply sup_le
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨ha, (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).zero_mem⟩
      · apply Subring.closure_le.mpr
        rintro _ rfl
        exact ⟨(Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).zero_mem, (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).one_mem⟩
    exact hle hz
  · rintro ⟨hr, hi⟩
    exact Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff F d v z hr hi

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients
