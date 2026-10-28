import OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients
import OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedCharacter

/-! # Integral Quadratic Ideles -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralQuadraticIdeles

noncomputable section

/-! The product of the integral quadratic unit groups away from the
finitely many nonintegral parameters maps continuously into the actual
quadratic ideles. -/

open scoped Classical _root_.NumberField
open Filter IsDedekindDomain

open OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedCharacter.Construction OAI.RepresentationTheory.Theta.Adelic.QuadraticIntegralCoefficients

def orderUnits {R : Type*} [CommRing R] (S : Subring R) : Subgroup Rˣ where
  carrier := {a | a.val ∈ S ∧ a.inv ∈ S}
  one_mem' := ⟨S.one_mem, S.one_mem⟩
  mul_mem' := fun ha hb => ⟨S.mul_mem ha.1 hb.1, S.mul_mem hb.2 ha.2⟩
  inv_mem' := fun ha => ⟨ha.2, ha.1⟩

variable (F : Type) [Field F] [NumberField F] (d : F)

abbrev FinitePlace := HeightOneSpectrum (𝓞 F)

def goodIntegralUnits (v : FinitePlace F) : Subgroup (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v))ˣ :=
  if Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) then
    orderUnits (Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v)) else ⊥

theorem goodIntegralUnits_coeff (v : FinitePlace F) (a : goodIntegralUnits F d v) :
    a.val.val.re ∈ v.adicCompletionIntegers F ∧
      a.val.val.im ∈ v.adicCompletionIntegers F := by
  by_cases hd : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)
  · have ha : a.val.val ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v) := by
      have h := a.property
      change a.val ∈ (if Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) then
        orderUnits (Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v)) else ⊥) at h
      rw [ite_eq_left hd] at h
      exact h.1
    exact (QuadraticIntegralCoefficients.quadraticOrder_coefficients F d (.inr v) hd _).mp ha
  · have ha : a.val = 1 := by
      have h := a.property
      change a.val ∈ (if Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) then
        orderUnits (Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v)) else ⊥) at h
      rw [ite_eq_right hd, Subgroup.mem_bot] at h
      exact h
    rw [ha]
    exact ⟨(v.adicCompletionIntegers F).one_mem, (v.adicCompletionIntegers F).zero_mem⟩

abbrev IntegralUnitProduct := ∀ v : FinitePlace F, goodIntegralUnits F d v

def realDifference (a : IntegralUnitProduct F d) (v : FinitePlace F) :
    v.adicCompletionIntegers F :=
  ⟨(a v).val.val.re - 1,
    (v.adicCompletionIntegers F).sub_mem (goodIntegralUnits_coeff F d v (a v)).1
      (v.adicCompletionIntegers F).one_mem⟩

def imaginaryPart (a : IntegralUnitProduct F d) (v : FinitePlace F) :
    v.adicCompletionIntegers F :=
  ⟨(a v).val.val.im, (goodIntegralUnits_coeff F d v (a v)).2⟩

def productValue (a : IntegralUnitProduct F d) : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d :=
  ⟨Weil.AdelicSplitting.UnramifiedCharacter.Construction.integralFiniteAdeles F (realDifference F d a) + 1,
    Weil.AdelicSplitting.UnramifiedCharacter.Construction.integralFiniteAdeles F (imaginaryPart F d a)⟩

@[simp] theorem productValue_finite (a : IntegralUnitProduct F d) (v : FinitePlace F) :
    Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticEvaluate F d (.inr v) (productValue F d a) = (a v).val.val := by
  apply QuadraticAlgebra.ext
  · change (a v).val.val.re - 1 + 1 = _
    exact sub_add_cancel _ _
  · rfl

@[simp] theorem productValue_infinite (a : IntegralUnitProduct F d)
    (v : NumberField.InfinitePlace F) :
    Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticEvaluate F d (.inl v) (productValue F d a) = 1 := by
  apply QuadraticAlgebra.ext
  · change (0 : v.Completion) + 1 = 1
    exact zero_add _
  · rfl

def productIdele : IntegralUnitProduct F d →* (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ where
  toFun a :=
    { val := productValue F d a
      inv := productValue F d a⁻¹
      val_inv := by
        apply Weil.AdelicSplitting.Characters.Construction.quadraticAdeles_ext F d
        intro v
        rw [map_mul, map_one]
        cases v with
        | inl v => exact (congrArg₂ (· * ·) (productValue_infinite F d a v)
            (productValue_infinite F d a⁻¹ v)).trans (one_mul 1)
        | inr v => exact (congrArg₂ (· * ·) (productValue_finite F d a v)
            (productValue_finite F d a⁻¹ v)).trans (a v).val.val_inv
      inv_val := by
        apply Weil.AdelicSplitting.Characters.Construction.quadraticAdeles_ext F d
        intro v
        rw [map_mul, map_one]
        cases v with
        | inl v => exact (congrArg₂ (· * ·) (productValue_infinite F d a⁻¹ v)
            (productValue_infinite F d a v)).trans (one_mul 1)
        | inr v => exact (congrArg₂ (· * ·) (productValue_finite F d a⁻¹ v)
            (productValue_finite F d a v)).trans (a v).val.inv_val }
  map_one' := by
    apply Units.ext
    apply Weil.AdelicSplitting.Characters.Construction.quadraticAdeles_ext F d
    intro v
    change Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticEvaluate F d v (productValue F d 1) = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticEvaluate F d v 1
    rw [map_one]
    cases v with
    | inl v => exact productValue_infinite F d 1 v
    | inr v => exact productValue_finite F d 1 v
  map_mul' a b := by
    apply Units.ext
    apply Weil.AdelicSplitting.Characters.Construction.quadraticAdeles_ext F d
    intro v
    change Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticEvaluate F d v (productValue F d (a * b)) =
      Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticEvaluate F d v (productValue F d a * productValue F d b)
    rw [map_mul]
    cases v with
    | inl v =>
      exact (productValue_infinite F d (a * b) v).trans
        ((one_mul 1).symm.trans (congrArg₂ (· * ·) (productValue_infinite F d a v)
          (productValue_infinite F d b v)).symm)
    | inr v =>
      exact (productValue_finite F d (a * b) v).trans
        (congrArg₂ (· * ·) (productValue_finite F d a v)
          (productValue_finite F d b v)).symm

theorem productValue_continuous : Continuous (productValue F d) := by
  have hr : Continuous (realDifference F d) := continuous_pi fun v =>
    (((Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_re _).comp
      (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v)))).sub
        continuous_const).subtype_mk _
  have hi : Continuous (imaginaryPart F d) := continuous_pi fun v =>
    ((Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_im _).comp
      (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v)))).subtype_mk _
  rw [Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
  exact ⟨((Weil.AdelicSplitting.UnramifiedCharacter.Construction.integralFiniteAdeles_continuous F).comp hr).add continuous_const,
    (Weil.AdelicSplitting.UnramifiedCharacter.Construction.integralFiniteAdeles_continuous F).comp hi⟩

theorem productIdele_continuous : Continuous (productIdele F d) := by
  apply Units.continuous_iff.mpr
  exact ⟨productValue_continuous F d, (productValue_continuous F d).comp continuous_inv⟩

theorem productIdele_single (v : FinitePlace F) (a : goodIntegralUnits F d v) :
    productIdele F d (Pi.mulSingle v a) = Weil.AdelicSplitting.Characters.Construction.localIdele F d (.inr v) a.val := by
  apply Units.ext
  apply Weil.AdelicSplitting.Characters.Construction.quadraticAdeles_ext F d
  intro w
  change Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticEvaluate F d w (productValue F d (Pi.mulSingle v a)) =
    Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticEvaluate F d w (Weil.AdelicSplitting.Characters.Construction.localIdeleElement F d (.inr v) a.val).val
  cases w with
  | inl w =>
    exact (productValue_infinite F d _ w).trans
      (Weil.AdelicSplitting.Characters.Construction.quadraticEvaluate_localIdele_other F d Sum.inl_ne_inr a.val).symm
  | inr w =>
    calc
      _ = ((Pi.mulSingle v a : IntegralUnitProduct F d) w).val.val :=
        productValue_finite F d _ w
      _ = _ := by
        by_cases h : w = v
        · subst w
          rw [Pi.mulSingle_eq_same]
          exact (Weil.AdelicSplitting.Characters.Construction.quadraticEvaluate_localIdele_same F d (.inr v) a.val).symm
        · rw [Pi.mulSingle_eq_of_ne h]
          exact (Weil.AdelicSplitting.Characters.Construction.quadraticEvaluate_localIdele_other F d
            (show Sum.inr w ≠ Sum.inr v from by simpa using h) a.val).symm

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralQuadraticIdeles
