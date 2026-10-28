import OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryAlgebra
import OAI.RepresentationTheory.Weil.AdelicSplitting.Integral

/-! # Integral Scalar Family -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.IntegralScalarFamily.RationalFamily

/-! A fixed rational norm-one scalar family with unit differences.
Its values, inverse values, and all scalar differences are integral at
almost every place. -/

open scoped Classical _root_.NumberField
open Filter

variable (F : Type) [Field F] [NumberField F] (d : F) (hns : ¬ IsSquare d)

abbrev nonsquareFact : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := ⟨by
  intro r hr
  apply hns
  exact ⟨r, by simpa only [pow_two, zero_mul, add_zero] using hr.symm⟩⟩

def rationalScalarUnit (t : F) : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ :=
  let : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := nonsquareFact F d hns
  Units.mk0 (Weil.AdelicSplitting.UnitaryAlgebra.Construction.cayleyScalar d t) (Weil.AdelicSplitting.UnitaryAlgebra.Construction.cayleyScalar_ne_zero d t)

theorem rationalScalarUnit_unitary (t : F) :
    star (rationalScalarUnit F d hns t).val * (rationalScalarUnit F d hns t).val = 1 := by
  let : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := nonsquareFact F d hns
  exact Weil.AdelicSplitting.UnitaryAlgebra.Construction.cayleyScalar_unitary d t

theorem rationalScalarUnit_ne_one (t : F) : (rationalScalarUnit F d hns t).val ≠ 1 := by
  let : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := nonsquareFact F d hns
  intro h
  change Weil.AdelicSplitting.UnitaryAlgebra.Construction.cayleyScalar d t = 1 at h
  have he := (div_eq_one_iff_eq (star_ne_zero.mpr (Weil.AdelicSplitting.UnitaryAlgebra.Construction.cayleyNumerator_ne_zero d t))).mp h
  have hi : (1 : F) = -1 := congrArg QuadraticAlgebra.im he
  have : (2 : F) = 0 := by linear_combination hi
  exact two_ne_zero this

theorem rationalScalarUnit_injective : Function.Injective (fun t => (rationalScalarUnit F d hns t).val) := by
  let : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := nonsquareFact F d hns
  exact Weil.AdelicSplitting.UnitaryAlgebra.Construction.cayleyScalar_injective d

def scalarDifference (s t : F) (hst : s ≠ t) : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ :=
  let : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := nonsquareFact F d hns
  Units.mk0 ((rationalScalarUnit F d hns s).val - (rationalScalarUnit F d hns t).val)
    (sub_ne_zero.mpr (fun h => hst (rationalScalarUnit_injective F d hns h)))

def scalarMinusOne (t : F) : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ :=
  let : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := nonsquareFact F d hns
  Units.mk0 ((rationalScalarUnit F d hns t).val - 1)
    (sub_ne_zero.mpr (rationalScalarUnit_ne_one F d hns t))

theorem rational_quadratic_unit_integral (u : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ) :
    ∀ᶠ v in cofinite,
      Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v u.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v ∧
      Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v u.inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v := by
  filter_upwards [Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal_integral F d u.val,
    Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal_integral F d u.inv] with v hv hi
  exact ⟨hv, hi⟩

end RepresentationTheory.Theta.Adelic.IntegralScalarFamily.RationalFamily

namespace RepresentationTheory.Theta.Adelic.IntegralScalarFamily.Family

/-! The fixed rational scalar family and all its unit differences are
integral simultaneously at almost every completion. -/

open Filter
open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.IntegralScalarFamily.RationalFamily

variable (F : Type) [Field F] [NumberField F] (d : F) (hns : ¬ IsSquare d) (R : ℕ)

def scalarFamily (i : Fin R) : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ := RationalFamily.rationalScalarUnit F d hns (i.val : F)

def localScalarFamily (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (i : Fin R) : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ :=
  Units.map (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v).toMonoidHom (scalarFamily F d hns R i)

theorem localScalarFamily_unitary (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (i : Fin R) :
    star (localScalarFamily F d hns R v i).val * (localScalarFamily F d hns R v i).val = 1 := by
  have h := congrArg (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v) (RationalFamily.rationalScalarUnit_unitary F d hns (i.val : F))
  rw [map_mul, map_one] at h
  change Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v) d (star (scalarFamily F d hns R i).val) *
    Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v (scalarFamily F d hns R i).val = 1 at h
  rw [Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star] at h
  exact h

structure IntegralScalarFamilyAt (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) : Prop where
  integral : ∀ i, (localScalarFamily F d hns R v i).val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v ∧
    (localScalarFamily F d hns R v i).inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v
  minus_one : ∀ i, ∃ u : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ,
    u.val = (localScalarFamily F d hns R v i).val - 1 ∧
      u.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v ∧ u.inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v
  differences : ∀ i j, i ≠ j → ∃ u : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ,
    u.val = (localScalarFamily F d hns R v i).val - (localScalarFamily F d hns R v j).val ∧
      u.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v ∧ u.inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v

theorem integralScalarFamilyAt_eventually :
    ∀ᶠ v in cofinite, IntegralScalarFamilyAt F d hns R v := by
  have hu : ∀ᶠ v in cofinite, ∀ i : Fin R,
      (localScalarFamily F d hns R v i).val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v ∧
      (localScalarFamily F d hns R v i).inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v :=
    Filter.eventually_all.mpr fun i => RationalFamily.rational_quadratic_unit_integral F d (scalarFamily F d hns R i)
  have h1 : ∀ᶠ v in cofinite, ∀ i : Fin R, ∃ u : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ,
      u.val = (localScalarFamily F d hns R v i).val - 1 ∧
      u.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v ∧ u.inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v := by
    apply Filter.eventually_all.mpr
    intro i
    let u := RationalFamily.scalarMinusOne F d hns (i.val : F)
    filter_upwards [RationalFamily.rational_quadratic_unit_integral F d u] with v hv
    refine ⟨Units.map (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v).toMonoidHom u, ?_, hv.1, hv.2⟩
    change Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v ((scalarFamily F d hns R i).val - 1) = _
    rw [map_sub, map_one]
    rfl
  have hdif : ∀ᶠ v in cofinite, ∀ i j : Fin R, i ≠ j → ∃ u : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ,
      u.val = (localScalarFamily F d hns R v i).val - (localScalarFamily F d hns R v j).val ∧
      u.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v ∧ u.inv ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => False.elim (h hij)
    · have hcast : (i.val : F) ≠ (j.val : F) := fun h => hij (Fin.ext (Nat.cast_injective h))
      let u := RationalFamily.scalarDifference F d hns (i.val : F) (j.val : F) hcast
      filter_upwards [RationalFamily.rational_quadratic_unit_integral F d u] with v hv
      intro _
      refine ⟨Units.map (Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v).toMonoidHom u, ?_, hv.1, hv.2⟩
      change Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d v ((scalarFamily F d hns R i).val -
        (scalarFamily F d hns R j).val) = _
      rw [map_sub]
      rfl
  filter_upwards [hu, h1, hdif] with v hv h1 hdif
  exact ⟨hv, h1, hdif⟩

end RepresentationTheory.Theta.Adelic.IntegralScalarFamily.Family

end

end OAI
