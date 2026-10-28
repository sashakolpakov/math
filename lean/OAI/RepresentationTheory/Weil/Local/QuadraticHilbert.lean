import OAI.RepresentationTheory.Weil.Local.QuadraticNormUnits
import OAI.RepresentationTheory.Weil.Local.QuadraticNormAt

/-! # Quadratic Hilbert -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticHilbert.Construction

noncomputable section

/-! The explicit quadratic Hilbert 90 map, with its scalar kernel and norm-one image. -/

variable {k : Type*} [Field k]

def quadraticNormKernelEquiv : (QuadraticNormUnits.Construction.quadraticNormUnits (k := k)).ker ≃* QuadraticNormAt.Construction.QuadraticNormOne k where
  toFun z := QuadraticNormUnits.Construction.quadraticNormOneOfUnit z.val z.property
  invFun p := ⟨QuadraticNormUnits.Construction.quadraticNormOneUnits p, QuadraticNormUnits.Construction.quadraticNormOneUnits_norm p⟩
  left_inv z := by apply Subtype.ext; exact QuadraticNormUnits.Construction.quadraticNormOneUnits_ofUnit z.val z.property
  right_inv p := by apply Subtype.ext; rfl
  map_mul' z w := by
    apply Subtype.ext
    apply Prod.ext <;> simp [QuadraticNormUnits.Construction.quadraticNormOneOfUnit, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticNormAt.Construction.QuadraticNormOne.mul_val]
    ring

def quadraticHilbert90 : (QuadraticNormUnits.Construction.QuadraticNormAlgebra k)ˣ →* QuadraticNormAt.Construction.QuadraticNormOne k :=
  quadraticNormKernelEquiv.toMonoidHom.comp
    (((MonoidHom.id (QuadraticNormUnits.Construction.QuadraticNormAlgebra k)ˣ) / QuadraticNormUnits.Construction.quadraticConjugateUnits).codRestrict
      QuadraticNormUnits.Construction.quadraticNormUnits.ker (fun z => by
        change QuadraticNormUnits.Construction.quadraticNormUnits (z / QuadraticNormUnits.Construction.quadraticConjugateUnits z) = 1
        rw [map_div, QuadraticNormUnits.Construction.quadraticNormUnits_conjugate, div_self']))

theorem quadraticHilbert90_embed (z : (QuadraticNormUnits.Construction.QuadraticNormAlgebra k)ˣ) :
    QuadraticNormUnits.Construction.quadraticNormOneUnits (quadraticHilbert90 z) = z / QuadraticNormUnits.Construction.quadraticConjugateUnits z := by
  apply Units.ext
  exact QuadraticAlgebra.mk_eta _

theorem quadraticHilbert90_scalar (a : kˣ) : quadraticHilbert90 (QuadraticNormUnits.Construction.quadraticScalarUnits a) = 1 := by
  apply QuadraticNormUnits.Construction.quadraticNormOneUnits_injective
  rw [quadraticHilbert90_embed, QuadraticNormUnits.Construction.quadraticConjugateUnits_scalar, div_self', map_one]

theorem quadraticHilbert90_normOne (p : QuadraticNormAt.Construction.QuadraticNormOne k) :
    quadraticHilbert90 (QuadraticNormUnits.Construction.quadraticNormOneUnits p) = p ^ 2 := by
  apply QuadraticNormUnits.Construction.quadraticNormOneUnits_injective
  rw [quadraticHilbert90_embed, QuadraticNormUnits.Construction.quadraticNormOneUnits_conjugate, map_pow, div_inv_eq_mul, pow_two]

theorem quadraticHilbert90_kernel [CharZero k] (z : (QuadraticNormUnits.Construction.QuadraticNormAlgebra k)ˣ) :
    quadraticHilbert90 z = 1 ↔ ∃ a : kˣ, QuadraticNormUnits.Construction.quadraticScalarUnits a = z := by
  constructor
  · intro hz
    have he := congrArg QuadraticNormUnits.Construction.quadraticNormOneUnits hz
    rw [quadraticHilbert90_embed, map_one, div_eq_one] at he
    have hi : z.val.im = -z.val.im := congrArg (fun w : (QuadraticNormUnits.Construction.QuadraticNormAlgebra k)ˣ => w.val.im) he
    have hi0 : z.val.im = 0 := by linear_combination (1 / 2 : k) * hi
    have hr0 : z.val.re ≠ 0 := by
      intro hr
      apply z.ne_zero
      ext <;> simp [hr, hi0]
    refine ⟨Units.mk0 z.val.re hr0, ?_⟩
    apply Units.ext
    ext
    · rfl
    · exact hi0.symm
  · rintro ⟨a, rfl⟩
    exact quadraticHilbert90_scalar a

theorem quadraticHilbert90_surjective [CharZero k] :
    Function.Surjective (quadraticHilbert90 (k := k)) := by
  intro p
  by_cases hp : p = QuadraticNormAt.Construction.QuadraticNormOne.minusOne
  · let t : QuadraticNormAt.Construction.QuadraticNormOne k := ⟨(0, 1), by simp⟩
    refine ⟨QuadraticNormUnits.Construction.quadraticNormOneUnits t, ?_⟩
    rw [quadraticHilbert90_normOne, hp]
    apply Subtype.ext
    simp [t, pow_two, QuadraticNormAt.Construction.QuadraticNormOne.minusOne]
  · let q := (QuadraticNormUnits.Construction.quadraticNormOneUnits p).val
    let z : QuadraticNormUnits.Construction.QuadraticNormAlgebra k := 1 + q
    have hpN : p.val.1 ^ 2 + p.val.2 ^ 2 = 1 := p.property
    have hNz : QuadraticAlgebra.norm z = 2 * (1 + p.val.1) := by
      rw [QuadraticNormUnits.Construction.quadraticAlgebra_norm]
      change (1 + p.val.1) ^ 2 + (0 + p.val.2) ^ 2 = 2 * (1 + p.val.1)
      linear_combination hpN
    have hu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
      (isUnit_iff_ne_zero.mpr (by
        rw [hNz]
        exact mul_ne_zero (by norm_num) (QuadraticNormAt.Construction.quadraticNormOne_re_ne_neg_one p hp)))
    refine ⟨hu.unit, ?_⟩
    apply QuadraticNormUnits.Construction.quadraticNormOneUnits_injective
    rw [quadraticHilbert90_embed, div_eq_iff_eq_mul]
    apply Units.ext
    change hu.unit.val = q * star hu.unit.val
    rw [hu.unit_spec]
    have hq : q * star q = 1 := by
      rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
      have hn : QuadraticAlgebra.norm q = 1 := congrArg Units.val (QuadraticNormUnits.Construction.quadraticNormOneUnits_norm p)
      rw [hn, map_one]
    change 1 + q = q * star (1 + q)
    rw [star_add, star_one, mul_add, mul_one, hq, add_comm]

end

end OAI.RepresentationTheory.Weil.Local.QuadraticHilbert.Construction
