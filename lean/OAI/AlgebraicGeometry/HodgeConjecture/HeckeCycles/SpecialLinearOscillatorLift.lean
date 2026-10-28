import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Commutators

/-! # Special Linear Oscillator Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialLinearOscillatorLift.CM

noncomputable section

/-! Every actual homomorphic SL3 oscillator action takes values in the
intrinsic metaplectic subgroup, since elementary matrices are commutators. -/

open scoped Classical commutatorElement
open _root_.Matrix.SpecialLinearGroup

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group

variable {I K : Type*} [Fintype I] [Field K]
  (f : Matrix.SpecialLinearGroup (Fin 3) K →* Finite.FiniteOscillator.CM.Oscillator (I := I))

theorem mem_bare (g : Matrix.SpecialLinearGroup (Fin 3) K) : f g ∈ Finite.BareNe.CM.Group.bareSubgroup := by
  apply Geometry.ComplexBall.Generation.ArithmeticQuotient.sl3_transvection_induction
    (fun g : Matrix.SpecialLinearGroup (Fin 3) K => f g ∈ Finite.BareNe.CM.Group.bareSubgroup) _ _ g
  · intro i j hij a
    obtain ⟨k, hik, hkj⟩ : ∃ k : Fin 3, i ≠ k ∧ k ≠ j := by
      fin_cases i <;> fin_cases j <;> decide
    rw [CMExtraction.Commutators.Local.sl3_transvection_commutator hij hik hkj a, map_commutatorElement]
    exact Subgroup.subset_closure (Or.inl ⟨f (transvection hik a), f (transvection hkj (1 : K)), rfl⟩)
  · intro a b ha hb
    rw [map_mul]
    exact Finite.BareNe.CM.Group.bareSubgroup.mul_mem ha hb

def lift : Matrix.SpecialLinearGroup (Fin 3) K →* Finite.BareNe.CM.Group.BareGroup (I := I) where
  toFun g := ⟨f g, mem_bare f g⟩
  map_one' := Subtype.ext f.map_one
  map_mul' g h := Subtype.ext (f.map_mul g h)

theorem projection (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    Finite.BareNe.CM.Group.bareProjection (lift f g) = Finite.FiniteOscillator.CM.projection (f g) := rfl

theorem action (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    Finite.BareNe.CM.Group.bareAction (lift f g) = Finite.FiniteOscillator.CM.action (f g) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialLinearOscillatorLift.CM
