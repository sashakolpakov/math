import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.FiniteModuleFieldDetection
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Unramified.Basic

/-! # Field Base Change Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FieldBaseChangeCriterion

noncomputable section

/-! An algebra essentially of finite type is formally unramified if every field-valued base change is formally unramified. -/

open scoped TensorProduct

universe u

theorem algebra_formallyUnramified_of_fieldBaseChanges
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], Algebra.FormallyUnramified K (K ⊗[R] S)) :
    Algebra.FormallyUnramified R S := by
  constructor
  apply Relative.FiniteModuleFieldDetection.finiteAlgebraModule_subsingleton_of_fieldTensors R S Ω[S⁄R]
  intro K _ _
  let : Algebra S (K ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.FormallyUnramified K (K ⊗[R] S) := h K
  exact (KaehlerDifferential.tensorKaehlerEquivBase R K S (K ⊗[R] S)).injective.subsingleton

theorem algebra_formallyUnramified_of_rightFieldBaseChanges
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    (h : ∀ (K : Type u) [Field K] [Algebra R K],
      letI : Algebra K (S ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
      Algebra.FormallyUnramified K (S ⊗[R] K)) : Algebra.FormallyUnramified R S := by
  constructor
  apply Relative.FiniteModuleFieldDetection.finiteAlgebraModule_subsingleton_of_fieldTensors R S Ω[S⁄R]
  intro K _ _
  let : Algebra K (S ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.FormallyUnramified K (S ⊗[R] K) := h K
  exact (KaehlerDifferential.tensorKaehlerEquivBase R K S (S ⊗[R] K)).injective.subsingleton

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FieldBaseChangeCriterion
