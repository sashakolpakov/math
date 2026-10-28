import OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection

/-! # Base Local Idele -/

namespace OAI.RepresentationTheory.Theta.Adelic.BaseLocalIdele

noncomputable section

/-! The actual base-field local idele and its compatibility with the
quadratic local scalar idele used by AdelicSplitting's character restrictions. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection

variable (F : Type) [Field F] [NumberField F] (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)

def baseLocalIdeleElement (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ) : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ where
  val := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localAdd F v (a.val - 1) + 1
  inv := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localAdd F v (a.inv - 1) + 1
  val_inv := by
    apply Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adeles_ext F
    intro w
    by_cases h : w = v
    · subst w
      simp only [map_mul, map_add, map_one, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate_localAdd_same, sub_add_cancel, a.val_inv]
    · simp [Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate_localAdd_other F h]
  inv_val := by
    apply Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adeles_ext F
    intro w
    by_cases h : w = v
    · subst w
      simp only [map_mul, map_add, map_one, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate_localAdd_same, sub_add_cancel, a.inv_val]
    · simp [Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate_localAdd_other F h]

def baseLocalIdele : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ →* (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ where
  toFun := baseLocalIdeleElement F v
  map_one' := by apply Units.ext; simp [baseLocalIdeleElement]
  map_mul' a b := by
    apply Units.ext
    apply Weil.AdelicSplitting.ArchimedeanAdeles.Construction.adeles_ext F
    intro w
    by_cases h : w = v
    · subst w
      simp [baseLocalIdeleElement]
    · simp [baseLocalIdeleElement, Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate_localAdd_other F h]

theorem baseLocalIdele_continuous : Continuous (baseLocalIdele F v) := by
  apply Units.continuous_iff.mpr
  exact ⟨((Weil.AdelicSplitting.Characters.Construction.localAdd_continuous F v).comp (Units.continuous_val.sub continuous_const)).add continuous_const,
    ((Weil.AdelicSplitting.Characters.Construction.localAdd_continuous F v).comp (Units.continuous_coe_inv.sub continuous_const)).add continuous_const⟩

theorem scalar_local_idele (d : F) (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ) :
    IdeleClassInjection.scalarIdele F d (baseLocalIdele F v a) = Weil.AdelicSplitting.Characters.Construction.localIdele F d v (Weil.AdelicSplitting.Characters.Construction.localScalarIdele F d v a) := by
  apply Units.ext
  apply QuadraticAlgebra.ext
  · rfl
  · change 0 = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localAdd F v (0 - 0) + 0
    simp

end

end OAI.RepresentationTheory.Theta.Adelic.BaseLocalIdele
