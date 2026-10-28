import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.AdelicClosure
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.StrongApproximation

/-! # Positive Closure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PositiveClosure

noncomputable section

/-! Apply proved quaternion strong approximation before specializing
the field and its local topologies to the CM presentation. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

theorem quaternion_image_closure_of_positive
    (F : Type) [Field F] [NumberField F] (a b : F)
    (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a))ˣ)
    (hH : H.val = UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b))
    (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F)
    {G : Type*} [Group G] [TopologicalSpace G]
    (p : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)) →ₜ* G)
    (ha : a ≠ 0) (hb : -b ≠ 0)
    (w : NumberField.InfinitePlace F)
    (e : NumberTheory.Quaternion.Arithmetic.LocalAdeles.Completion (Sum.inl w : NumberTheory.Quaternion.Arithmetic.LocalAdeles.Place F) ≃+* ℝ) (he : Continuous e)
    (hpos : 0 < e (NumberTheory.Quaternion.Arithmetic.LocalAdeles.localEmbedding (Sum.inl w) (-b)))
    (y : G)
    (hy : ∃ g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v),
      p (HermitianAdeles.quaternionLocalHermitian F a b H hH v g) = y) :
    (y, 1) ∈ closure
      (Set.range (fun z : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val => ActiveAwayProjection.Approximation.activeAwayProjection F H v p (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU F H z))) :=
  AdelicClosure.quaternion_image_mem_closure F a b H hH v p
    (StrongApproximation.quaternion_finite_strongApproximation_positive a (-b) ha hb w e he hpos) y hy

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PositiveClosure
