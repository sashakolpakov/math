import OAI.RepresentationTheory.Weil.AdelicSplitting.Characters
import OAI.NumberTheory.Adeles.LocalCompletions

/-! # Idele Class Injection -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.IdeleClassInjection

/-! The scalar map embeds base idele classes into the actual quadratic
adelic idele quotient. The principal-point intersection is proved in
coefficients; closedness and properness are separate remaining steps. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.Characters.Construction

variable (F : Type) [Field F] [NumberField F] (d : F)

def scalarIdele : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ →* (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ :=
  Units.map (algebraMap (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)).toMonoidHom

def quadraticPrincipal : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ →* (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ :=
  Units.map (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticRational F d).toMonoidHom

abbrev QuadraticIdeleClass := (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ ⧸ (quadraticPrincipal F d).range

theorem quadraticRational_injective : Function.Injective (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.quadraticRational F d) := by
  intro a b hab
  apply QuadraticAlgebra.ext
  · exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F
      (congrArg QuadraticAlgebra.re hab)
  · exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F
      (congrArg QuadraticAlgebra.im hab)

theorem quadraticPrincipal_injective : Function.Injective (quadraticPrincipal F d) := by
  intro a b hab
  apply Units.ext
  exact quadraticRational_injective F d (congrArg Units.val hab)

theorem principal_intersection (x : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ) :
    scalarIdele F d x ∈ (quadraticPrincipal F d).range ↔
      x ∈ (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F).range := by
  constructor
  · rintro ⟨a, ha⟩
    have him : algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) a.val.im = 0 :=
      congrArg (fun z : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ => z.val.im) ha
    have hi : a.val.im = 0 :=
      NumberField.AdeleRing.algebraMap_injective (𝓞 F) F (him.trans (map_zero _).symm)
    have hre : algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) a.val.re = x.val :=
      congrArg (fun z : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ => z.val.re) ha
    have hn : a.val.re ≠ 0 := by
      intro hz
      apply a.ne_zero
      apply QuadraticAlgebra.ext
      · exact hz
      · exact hi
    refine ⟨Units.mk0 a.val.re hn, ?_⟩
    exact Units.ext hre
  · rintro ⟨a, rfl⟩
    refine ⟨Units.map (algebraMap F (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)).toMonoidHom a, ?_⟩
    apply Units.ext
    apply QuadraticAlgebra.ext <;> rfl

theorem principal_comap :
    (quadraticPrincipal F d).range.comap (scalarIdele F d) =
      (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F).range :=
  Subgroup.ext (principal_intersection F d)

def scalarIdeleClass : NumberTheory.Adeles.LocalCompletions.CompletionFactors.IdeleClass F →* QuadraticIdeleClass F d :=
  QuotientGroup.map (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F).range
    (quadraticPrincipal F d).range (scalarIdele F d) (principal_comap F d).ge

theorem scalarIdeleClass_injective : Function.Injective (scalarIdeleClass F d) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [scalarIdeleClass, QuotientGroup.ker_map, principal_comap]
  exact QuotientGroup.map_mk'_self _

theorem scalarIdele_continuous : Continuous (scalarIdele F d) := by
  apply Units.continuous_iff.mpr
  constructor
  · rw [Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
    exact ⟨Units.continuous_val, continuous_const⟩
  · rw [Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
    exact ⟨Units.continuous_coe_inv, continuous_const⟩

theorem scalarIdeleClass_continuous : Continuous (scalarIdeleClass F d) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  change Continuous (fun x : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ =>
    QuotientGroup.mk' (quadraticPrincipal F d).range (scalarIdele F d x))
  exact continuous_quotient_mk'.comp (scalarIdele_continuous F d)

end RepresentationTheory.Theta.Adelic.IdeleClassInjection

namespace RepresentationTheory.Theta.Adelic.IdeleClassInjection.ScalarFixed

/-! Scalar ideles are exactly the conjugation-fixed units in the quadratic
adelic algebra. This uses its actual coefficient algebra and topology. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.Characters.Construction OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection

variable (F : Type) [Field F] [NumberField F] (d : F)

theorem scalarIdele_star (x : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ) : star (scalarIdele F d x) = scalarIdele F d x := by
  apply Units.ext
  apply QuadraticAlgebra.ext <;> simp [scalarIdele, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

theorem scalarIdele_range_iff (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) :
    a ∈ (scalarIdele F d).range ↔ star a = a := by
  constructor
  · rintro ⟨x, rfl⟩
    exact scalarIdele_star F d x
  · intro ha
    have him : -a.val.im = a.val.im := congrArg (fun b : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ => b.val.im) ha
    have hi : a.val.im = 0 := by
      have hz : (2 : F) • a.val.im = 0 := by
        rw [two_smul]
        exact (add_eq_zero_iff_eq_neg).mpr him.symm
      have h := congrArg (fun z : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F => (2 : F)⁻¹ • z) hz
      simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : F) ≠ 0), one_smul, smul_zero] using h
    let x : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ :=
      { val := a.val.re
        inv := a.inv.re
        val_inv := by
          have h := congrArg QuadraticAlgebra.re a.val_inv
          simpa only [QuadraticAlgebra.re_mul, hi, mul_zero, zero_mul, add_zero,
            QuadraticAlgebra.re_one] using h
        inv_val := by
          have h := congrArg QuadraticAlgebra.re a.inv_val
          simpa only [QuadraticAlgebra.re_mul, hi, mul_zero, zero_mul, add_zero,
            QuadraticAlgebra.re_one] using h }
    refine ⟨x, ?_⟩
    apply Units.ext
    apply QuadraticAlgebra.ext
    · rfl
    · exact hi.symm

def conjugationRatio : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →* (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ where
  toFun a := a / star a
  map_one' := by simp
  map_mul' a b := by
    simp only [star_mul, div_eq_mul_inv, mul_inv_rev]
    ac_rfl

theorem conjugationRatio_norm_one (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) :
    conjugationRatio F d a * star (conjugationRatio F d a) = 1 := by
  simp only [conjugationRatio, MonoidHom.coe_mk, OneHom.coe_mk, star_div, star_star]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem conjugationRatio_eq_one_iff (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) :
    conjugationRatio F d a = 1 ↔ a ∈ (scalarIdele F d).range := by
  rw [scalarIdele_range_iff]
  change a / star a = 1 ↔ star a = a
  exact div_eq_one.trans eq_comm

theorem quadraticPrincipal_star (a : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ) :
    quadraticPrincipal F d (star a) = star (quadraticPrincipal F d a) := by
  apply Units.ext
  exact Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange_star (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)) d a.val

theorem conjugationRatio_principal (a : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)ˣ) :
    conjugationRatio F d (quadraticPrincipal F d a) = quadraticPrincipal F d (a / star a) := by
  rw [map_div, quadraticPrincipal_star]
  rfl

theorem conjugationRatio_continuous : Continuous (conjugationRatio F d) := by
  change Continuous (fun a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ => a * (star a)⁻¹)
  exact continuous_id.mul continuous_star.inv

end RepresentationTheory.Theta.Adelic.IdeleClassInjection.ScalarFixed

end

end OAI
