import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
import OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization

/-! # Split Norm -/

namespace OAI.RepresentationTheory.Theta.Adelic.SplitNorm

noncomputable section

/-! In root coordinates the quadratic norm is the product of the two
components. In particular the actual norm-kernel character at a split
place is trivial. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization.Construction OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra

variable {k : Type*} [Field k] [CharZero k] {d : k}
    (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)

theorem norm_eq_components (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    QuadraticAlgebra.norm z = SpecialUnitary.SplitAlgebra.plus r hr hr0 z * SpecialUnitary.SplitAlgebra.minus r hr hr0 z := by
  rcases z with ⟨a, b⟩
  change a * a + 0 * a * b - d * b * b = (a + r * b) * (a - r * b)
  rw [← hr]
  ring

def normPreimage (a : kˣ) : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ where
  val := (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm (a.val, 1)
  inv := (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm (a.inv, 1)
  val_inv := by rw [← map_mul]; simp
  inv_val := by rw [← map_mul]; simp

theorem normPreimage_spec (a : kˣ) : Units.map QuadraticAlgebra.norm (normPreimage r hr hr0 a) = a := by
  apply Units.ext
  change QuadraticAlgebra.norm ((SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm (a.val, 1)) = a.val
  rw [norm_eq_components r hr hr0]
  change ((SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0) ((SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm (a.val, 1))).1 *
    ((SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0) ((SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).symm (a.val, 1))).2 = a.val
  simp

theorem unit_eq_scalar_of_components (a : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ)
    (ha : SpecialUnitary.SplitAlgebra.plus r hr hr0 a.val = SpecialUnitary.SplitAlgebra.minus r hr hr0 a.val) :
    a = Units.map (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).toMonoidHom
      (Units.map (SpecialUnitary.SplitAlgebra.plus r hr hr0).toMonoidHom a) := by
  apply Units.ext
  apply (SpecialUnitary.SplitAlgebra.splitAlgebra r hr hr0).injective
  change (SpecialUnitary.SplitAlgebra.plus r hr hr0 a.val, SpecialUnitary.SplitAlgebra.minus r hr hr0 a.val) =
    (SpecialUnitary.SplitAlgebra.plus r hr hr0 a.val + r * 0, SpecialUnitary.SplitAlgebra.plus r hr hr0 a.val - r * 0)
  simp only [mul_zero, add_zero, sub_zero]
  exact Prod.ext rfl ha.symm

include r hr hr0 in
theorem norm_units_surjective : Function.Surjective
    (Units.map (QuadraticAlgebra.norm : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d →* k)) :=
  fun a => ⟨normPreimage r hr hr0 a, normPreimage_spec r hr hr0 a⟩

theorem normCharacter_split
    (F : Type) [Field F] [NumberField F] (d : F) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
    (r : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) (hr : r ^ 2 = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) (hr0 : r ≠ 0)
    (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ) : Weil.AdelicSplitting.Characters.Construction.normCharacter F d v a = 1 := by
  let : CharZero (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F v
  exact ite_eq_left (norm_units_surjective r hr hr0 a)

theorem normCharacterScalar_split
    (F : Type) [Field F] [NumberField F] (d : F) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
    (r : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) (hr : r ^ 2 = Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) (hr0 : r ≠ 0)
    (a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) : Weil.AdelicSplitting.Normalization.Construction.normCharacterScalar F d v a = 1 := by
  unfold Weil.AdelicSplitting.Normalization.Construction.normCharacterScalar
  split
  · exact normCharacter_split F d v r hr hr0 _
  · rfl

end

end OAI.RepresentationTheory.Theta.Adelic.SplitNorm
