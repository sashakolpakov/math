import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.HermitianAdeles
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveAwayProjection

/-! # Adelic Closure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.AdelicClosure

noncomputable section

section

/-! Transfer quaternion strong approximation to supported local elements
in the actual active/away special-unitary projection. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveAwayProjection.Approximation

variable (F : Type) [Field F] [NumberField F] (a b : F)
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
  (hH : H.val = UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b))
  (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)
  {G : Type*} [Group G] [TopologicalSpace G]
  (p : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) →ₜ* G)

theorem quaternion_supported_mem_closure
    (happrox : DenseRange (NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.diagonalFiniteAdelic (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b))))
    (g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v)) :
    (p (HermitianAdeles.quaternionLocalHermitian F a b H hH v g), 1) ∈
      closure (Set.range (fun z : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val => ActiveAwayProjection.Approximation.activeAwayProjection F H v p (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H z))) := by
  let f := (ActiveAwayProjection.Approximation.activeAwayProjection F H v p).comp (HermitianAdeles.quaternionFiniteHermitian F a b H hH)
  have hx := ActiveAwayProjection.Approximation.dense_diagonal_image_mem_closure
    (NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.diagonalFiniteAdelic (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b))) happrox f f.continuous
    (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (fun w => NumberTheory.Quaternion.Arithmetic.LocalAdeles.integralLocalSubgroup (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr w)) v g)
  have he : f (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace
      (fun w => NumberTheory.Quaternion.Arithmetic.LocalAdeles.integralLocalSubgroup (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr w)) v g) =
      (p (HermitianAdeles.quaternionLocalHermitian F a b H hH v g), 1) := by
    change ActiveAwayProjection.Approximation.activeAwayProjection F H v p (HermitianAdeles.quaternionFiniteHermitian F a b H hH _) = _
    rw [HermitianAdeles.quaternionFiniteHermitian_includePlace, ActiveAwayProjection.Approximation.activeAwayProjection_include]
  rw [he] at hx
  apply closure_mono (s := Set.range (fun x => f (NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.diagonalFiniteAdelic _ x))) ?_ hx
  rintro y ⟨x, rfl⟩
  exact ⟨HermitianAdeles.quaternionRationalHermitian F a b H hH x,
    (congrArg (ActiveAwayProjection.Approximation.activeAwayProjection F H v p)
      (HermitianAdeles.quaternionFiniteHermitian_diagonal F a b H hH x)).symm⟩

end

/-! Transfer a local quaternion image witness to the supported closure
before specializing its coefficient field or Hermitian presentation. -/

open scoped Classical _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveAwayProjection.Approximation OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

theorem quaternion_image_mem_closure
    (F : Type) [Field F] [NumberField F] (a b : F)
    (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
    (hH : H.val = UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b))
    (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)
    {G : Type*} [Group G] [TopologicalSpace G]
    (p : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) →ₜ* G)
    (happrox : DenseRange (NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.diagonalFiniteAdelic (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b))))
    (y : G)
    (hy : ∃ g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v),
      p (HermitianAdeles.quaternionLocalHermitian F a b H hH v g) = y) :
    (y, 1) ∈ closure
      (Set.range (fun z : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val => ActiveAwayProjection.Approximation.activeAwayProjection F H v p (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H z))) := by
  obtain ⟨g, rfl⟩ := hy
  exact quaternion_supported_mem_closure F a b H hH v p happrox g

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.AdelicClosure
