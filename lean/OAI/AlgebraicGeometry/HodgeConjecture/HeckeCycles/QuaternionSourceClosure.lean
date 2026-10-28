import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.AdelicClosure

/-! # Quaternion Source Closure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuaternionSourceClosure.CM

noncomputable section

/-! Transfer quaternion supported closure through a surjective rational
source presentation before specializing the coefficient field. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.AdelicClosure
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU

theorem supported (F : Type) [Field F] [NumberField F] (a b : F)
    (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
    (hH : H.val = CMExtraction.UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b))
    (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)
    {G Γ : Type*} [Group G] [TopologicalSpace G] [Group Γ]
    (p : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) →ₜ* G)
    (e : Γ →* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val) (he : Function.Surjective e)
    (happrox : DenseRange (NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison.diagonalFiniteAdelic (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b))))
    (y : G) (hy : ∃ g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v),
      p (CMExtraction.Quaternion.HermitianAdeles.quaternionLocalHermitian F a b H hH v g) = y) :
    (y, 1) ∈ closure (Set.range
      ((CMExtraction.ActiveAwayProjection.Approximation.activeAwayProjection F H v p).toMonoidHom.comp ((RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H).comp e))) := by
  have h := CMExtraction.Quaternion.AdelicClosure.quaternion_image_mem_closure F a b H hH v p happrox y hy
  let t := fun g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val => CMExtraction.ActiveAwayProjection.Approximation.activeAwayProjection F H v p (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H g)
  have hr : Set.range
      ((CMExtraction.ActiveAwayProjection.Approximation.activeAwayProjection F H v p).toMonoidHom.comp ((RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H).comp e)) =
        Set.range t := he.range_comp t
  exact closure_mono hr.symm.subset h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuaternionSourceClosure.CM
