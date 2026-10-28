import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CokernelLength
import Mathlib.LinearAlgebra.Prod

/-! # Short Complex Colength -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ShortComplexColength

noncomputable section

/-! Colength comparison for a short complex and an auxiliary lift.
The comparison uses actual kernels and cokernels and works over any ring. -/

variable (R : Type*) [Ring R]
  {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]

def toCycles (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : g.comp f = 0) :
    A →ₗ[R] g.ker :=
  f.codRestrict g.ker (fun a => by
    change g (f a) = 0
    exact DFunLike.congr_fun h a)

def homologyToCokernel (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : g.comp f = 0) (t : C →ₗ[R] B) :
    (g.ker ⧸ (toCycles R f g h).range) →ₗ[R] B ⧸ (f.coprod t).range :=
  (toCycles R f g h).range.mapQ (f.coprod t).range g.ker.subtype (by
    rintro x ⟨a, rfl⟩
    exact ⟨(a, 0), by simp [toCycles]⟩)

theorem homologyToCokernel_injective (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : g.comp f = 0) (t : C →ₗ[R] B) (ht : Function.Injective (g.comp t)) :
    Function.Injective (homologyToCokernel R f g h t) := by
  let j := f.coprod t
  let k := toCycles R f g h
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨b, rfl⟩ := k.range.mkQ_surjective x
  have hb : (b : B) ∈ j.range := (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨⟨a, c⟩, hac⟩ := hb
  have hc : c = 0 := by
    apply ht
    change g (t c) = g (t 0)
    have he := congrArg g hac
    change g (f a + t c) = g b at he
    rw [map_add, show g (f a) = 0 from DFunLike.congr_fun h a,
      zero_add, b.property] at he
    simpa using he
  have hb' : b ∈ k.range := by
    refine ⟨a, Subtype.ext ?_⟩
    change f a = (b : B)
    simpa [j, hc] using hac
  exact (Submodule.Quotient.mk_eq_zero _).mpr hb'

theorem length_comparison (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : g.comp f = 0) (t : C →ₗ[R] B) (ht : Function.Injective (g.comp t)) :
    Module.length R (B ⧸ (f.coprod t).range) + Module.length R (C ⧸ g.range) =
      Module.length R (g.ker ⧸ (toCycles R f g h).range) +
        Module.length R (C ⧸ (g.comp t).range) := by
  let j := f.coprod t
  let k := toCycles R f g h
  let gt := g.rangeRestrict.comp t
  let u := homologyToCokernel R f g h t
  let v : (B ⧸ j.range) →ₗ[R] g.range ⧸ gt.range :=
    j.range.mapQ gt.range g.rangeRestrict (by
      rintro b ⟨⟨a, c⟩, rfl⟩
      refine ⟨c, ?_⟩
      apply Subtype.ext
      change g (t c) = g (f a + t c)
      rw [map_add, show g (f a) = 0 from DFunLike.congr_fun h a, zero_add])
  have hu : Function.Injective u := homologyToCokernel_injective R f g h t ht
  have hv : Function.Surjective v := by
    intro x
    obtain ⟨c, rfl⟩ := gt.range.mkQ_surjective x
    obtain ⟨b, hb⟩ := g.surjective_rangeRestrict c
    refine ⟨j.range.mkQ b, ?_⟩
    change gt.range.mkQ (g.rangeRestrict b) = _
    rw [hb]
  have he : Function.Exact u v := by
    rw [LinearMap.exact_iff]
    ext x
    obtain ⟨b, rfl⟩ := j.range.mkQ_surjective x
    constructor
    · intro hb
      have hg : g.rangeRestrict b ∈ gt.range := (Submodule.Quotient.mk_eq_zero _).mp hb
      obtain ⟨c, hc⟩ := hg
      have hb' : b - t c ∈ g.ker := by
        change g (b - t c) = 0
        rw [map_sub, sub_eq_zero]
        exact (congrArg Subtype.val hc).symm
      refine ⟨k.range.mkQ ⟨b - t c, hb'⟩, ?_⟩
      change j.range.mkQ (b - t c) = j.range.mkQ b
      rw [map_sub, sub_eq_self]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨(0, c), by simp [j]⟩
    · rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := k.range.mkQ_surjective y
      rw [← hy]
      change gt.range.mkQ (g.rangeRestrict a) = 0
      have ha : g.rangeRestrict a = 0 := Subtype.ext a.property
      rw [ha, map_zero]
  have hlen := Module.length_eq_add_of_exact u v hu hv he
  have hcomp := CokernelLength.length_cokernel_comp gt g.range.subtype
    g.range.subtype_injective
  have hmap : g.range.subtype.comp gt = g.comp t := rfl
  rw [hmap] at hcomp
  change Module.length R (B ⧸ j.range) =
    Module.length R (g.ker ⧸ k.range) + Module.length R (g.range ⧸ gt.range) at hlen
  rw [hlen, hcomp, add_assoc, Submodule.range_subtype]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ShortComplexColength
