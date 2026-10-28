import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Quotient Injective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.QuotientInjective

noncomputable section

/-! A nonzero principal quotient of a principal ideal domain is injective
as a module over itself. This applies to the finite Witt coefficient rings. -/

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

theorem baer (a : R) (ha : a ≠ 0) :
    Module.Baer (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a}) := by
  intro I f
  let S := R ⧸ Ideal.span {a}
  let q : R →+* S := Ideal.Quotient.mk (Ideal.span {a})
  let J := I.comap q
  let b := Submodule.IsPrincipal.generator J
  have hb : q b ∈ I := Submodule.IsPrincipal.generator_mem J
  have ha0 : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)
  have haJ : a ∈ J := by
    change q a ∈ I
    rw [ha0]
    exact I.zero_mem
  obtain ⟨c, hac⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd J).mp haJ
  have hc : c ≠ 0 := by
    intro h
    apply ha
    simpa only [h, mul_zero] using hac
  let bI : I := ⟨q b, hb⟩
  let y : S := f bI
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective y
  change q d = y at hd
  have hcb : q c • bI = 0 := by
    apply Subtype.ext
    change q c * q b = 0
    rw [← map_mul, mul_comm c b]
    exact (congrArg q hac).symm.trans ha0
  have hcy : q c * y = 0 := by
    change q c • f bI = 0
    rw [← f.map_smul, hcb, map_zero]
  have hcd : q (c * d) = 0 := by
    rw [map_mul, hd]
    exact hcy
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hcd)
  have hdt : d = b * t := by
    apply mul_left_cancel₀ hc
    calc
      c * d = a * t := ht
      _ = c * (b * t) := by rw [hac]; ring
  have hy : y = q b * q t := by
    rw [← hd, hdt, map_mul]
  let g : S →ₗ[S] S :=
    { toFun := fun x => x * q t
      map_add' := fun x z => add_mul x z (q t)
      map_smul' := fun r x => mul_assoc r x (q t) }
  refine ⟨g, ?_⟩
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hrJ : r ∈ J := hx
  obtain ⟨v, hrv⟩ := (Submodule.IsPrincipal.mem_iff_generator_dvd J).mp hrJ
  have hxI : (⟨q r, hx⟩ : I) = q v • bI := by
    apply Subtype.ext
    change q r = q v * q b
    rw [hrv, map_mul, mul_comm]
  change q r * q t = f ⟨q r, hx⟩
  rw [hxI, f.map_smul]
  change q r * q t = q v * y
  rw [hy, hrv, map_mul]
  ring

theorem injective (a : R) (ha : a ≠ 0) :
    Module.Injective (R ⧸ Ideal.span {a}) (R ⧸ Ideal.span {a}) :=
  (baer a ha).injective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.QuotientInjective
