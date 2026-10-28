import OAI.RepresentationTheory.Theta.Adelic.QuadraticHilbert
import OAI.RepresentationTheory.Weil.Local.SquareIndexTools

/-! # Quadratic Norm Square Quotient -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient

noncomputable section

/-! The algebraic square quotient for an arbitrary nonsplit quadratic
algebra. This is the local norm-index calculation's algebraic step. -/

open OAI.RepresentationTheory.Weil.Local.SquareIndexTools.Construction

variable {k : Type*} [Field k] (d : k)

def normUnits : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →* kˣ := Units.map QuadraticAlgebra.norm

def scalarUnits : kˣ →* (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ :=
  Units.map (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).toMonoidHom

def conjugateUnits : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →* (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ :=
  Units.map (starRingEnd (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).toMonoidHom

abbrev NormOne := (normUnits d).ker

theorem normUnits_scalar (a : kˣ) : normUnits d (scalarUnits d a) = a ^ 2 := by
  apply Units.ext
  exact QuadraticAlgebra.norm_algebraMap a.val

theorem conjugateUnits_scalar (a : kˣ) : conjugateUnits d (scalarUnits d a) = scalarUnits d a := by
  apply Units.ext
  ext <;> simp [conjugateUnits, scalarUnits, starRingEnd_apply]

theorem normUnits_conjugate (z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) : normUnits d (conjugateUnits d z) = normUnits d z := by
  apply Units.ext
  exact QuadraticAlgebra.norm_star z.val

theorem scalar_norm_eq_mul_conjugate (z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) :
    scalarUnits d (normUnits d z) = z * conjugateUnits d z := by
  apply Units.ext
  exact QuadraticAlgebra.algebraMap_norm_eq_mul_star z.val

theorem conjugate_normOne (p : NormOne d) : conjugateUnits d p.val = p.val⁻¹ := by
  have h : p.val * conjugateUnits d p.val = 1 := by
    rw [← scalar_norm_eq_mul_conjugate, show normUnits d p.val = 1 from p.property, map_one]
  exact eq_inv_of_mul_eq_one_right h

def hilbert90 : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →* NormOne d :=
  (((MonoidHom.id (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) / conjugateUnits d).codRestrict (normUnits d).ker
    (fun z => by
      change normUnits d (z / conjugateUnits d z) = 1
      rw [map_div, normUnits_conjugate, div_self']))

theorem hilbert90_scalar (a : kˣ) : hilbert90 d (scalarUnits d a) = 1 := by
  apply Subtype.ext
  change scalarUnits d a / conjugateUnits d (scalarUnits d a) = 1
  rw [conjugateUnits_scalar, div_self']

theorem hilbert90_normOne (p : NormOne d) : hilbert90 d p.val = p ^ 2 := by
  apply Subtype.ext
  change p.val / conjugateUnits d p.val = p.val ^ 2
  rw [conjugate_normOne, div_inv_eq_mul, pow_two]

theorem hilbert90_kernel [CharZero k] (z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) :
    hilbert90 d z = 1 ↔ ∃ a : kˣ, scalarUnits d a = z := by
  constructor
  · intro hz
    have he := congrArg Subtype.val hz
    change z / conjugateUnits d z = 1 at he
    rw [div_eq_one] at he
    have hi : z.val.im = -z.val.im := congrArg (fun w : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ => w.val.im) he
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
    exact hilbert90_scalar d a

theorem hilbert90_surjective [CharZero k] (hd : d ≠ 0) (hns : ¬ IsSquare d) :
    Function.Surjective (hilbert90 d) := by
  intro p
  have hp : p.val * star p.val = 1 := by
    change p.val * conjugateUnits d p.val = 1
    rw [conjugate_normOne, mul_inv_cancel]
  obtain ⟨z, hz⟩ := QuadraticHilbert.quadratic_hilbert90 d hd hns p.val hp
  exact ⟨z, Subtype.ext hz⟩

theorem hilbert90_mem_squares_iff [CharZero k] (z : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ) :
    hilbert90 d z ∈ Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (NormOne d) ↔ normUnits d z ∈ Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ := by
  constructor
  · rintro ⟨p, hp⟩
    change p ^ 2 = hilbert90 d z at hp
    have hk : hilbert90 d (z / p.val) = 1 := by
      rw [map_div, hilbert90_normOne, ← hp, div_self']
    obtain ⟨a, ha⟩ := (hilbert90_kernel d _).mp hk
    have hn := congrArg (normUnits d) ha
    rw [normUnits_scalar, map_div, show normUnits d p.val = 1 from p.property, div_one] at hn
    exact ⟨a, hn⟩
  · rintro ⟨a, ha⟩
    change a ^ 2 = normUnits d z at ha
    let w := z / scalarUnits d a
    have hw : normUnits d w = 1 := by
      change normUnits d (z / scalarUnits d a) = 1
      rw [map_div, normUnits_scalar, ← ha, div_self']
    let p : NormOne d := ⟨w, hw⟩
    have he : hilbert90 d w = hilbert90 d z := by
      change hilbert90 d (z / scalarUnits d a) = hilbert90 d z
      rw [map_div, hilbert90_scalar, div_one]
    refine ⟨p, ?_⟩
    change p ^ 2 = hilbert90 d z
    rw [← hilbert90_normOne]
    exact he

theorem norm_square_relIndex [CharZero k] (hd : d ≠ 0) (hns : ¬ IsSquare d) :
    (Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ).relIndex (normUnits d).range =
      (Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (NormOne d)).index := by
  have hcomap : (Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ).comap (normUnits d) =
      (Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (NormOne d)).comap (hilbert90 d) := by
    ext z
    exact (hilbert90_mem_squares_iff d z).symm
  rw [← Subgroup.index_comap, hcomap]
  exact Subgroup.index_comap_of_surjective _ (hilbert90_surjective d hd hns)

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient
