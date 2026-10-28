import OAI.AlgebraicGeometry.ComplexPoints.Analytic.Affine
import Mathlib.Topology.Algebra.Ring.Basic

/-! # Character Closed -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.CharacterClosed.Constructions

noncomputable section

/-! Actual complex algebra characters form a closed subspace of the
product of their evaluation coordinates, without finite generation. -/

variable (A : Type*) [CommRing A] [Algebra ℂ A]

theorem character_range :
    Set.range (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => (x : A → ℂ)) =
      {f : A → ℂ | f 0 = 0 ∧ f 1 = 1 ∧
        (∀ a b, f (a + b) = f a + f b) ∧
        (∀ a b, f (a * b) = f a * f b) ∧
        ∀ c : ℂ, f (algebraMap ℂ A c) = c} := by
  ext f
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.map_zero, x.map_one, x.map_add, x.map_mul, x.commutes⟩
  · rintro ⟨hz, ho, ha, hm, hc⟩
    exact ⟨{ toFun := f
             map_zero' := hz
             map_one' := ho
             map_add' := ha
             map_mul' := hm
             commutes' := hc }, rfl⟩

theorem isClosed_character_range :
    IsClosed (Set.range (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => (x : A → ℂ))) := by
  rw [character_range]
  simp_rw [Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_eq (continuous_apply 0) continuous_const).inter
    ((isClosed_eq (continuous_apply 1) continuous_const).inter
      ((isClosed_iInter fun a => isClosed_iInter fun b =>
        isClosed_eq (continuous_apply (a + b))
          ((continuous_apply a).add (continuous_apply b))).inter
        ((isClosed_iInter fun a => isClosed_iInter fun b =>
          isClosed_eq (continuous_apply (a * b))
            ((continuous_apply a).mul (continuous_apply b))).inter
          (isClosed_iInter fun c =>
            isClosed_eq (continuous_apply (algebraMap ℂ A c)) continuous_const))))

theorem isClosedEmbedding_character_coe :
    Topology.IsClosedEmbedding (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => (x : A → ℂ)) :=
  ⟨Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isEmbedding_coe, isClosed_character_range A⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.CharacterClosed.Constructions
