import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.GeneratorReconstruction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.UnitMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Generator Isogeny -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM

noncomputable section

/-! Every integral CM action sends the constructed primitive generator
to a finite étale isogeny with a fixed torsion bound for its kernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

theorem GeneratorIsogeny.integralAction_map_natCast {R : Type v} [CommRing R]
    {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (n : ℕ) :
    ρ.map (n : R) = (𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n := by
  induction n with
  | zero => simpa only [Nat.cast_zero, pow_zero] using ρ.map_zero
  | succ n ih => rw [Nat.cast_succ, ρ.map_add, ih, ρ.map_one, pow_succ]

variable {E : Type v} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem GeneratorReconstruction.CMIntegralGeneratorData.action_complements (D : GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) :
    ρ.map D.generator ≫ ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E D.generator) =
        (𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ (D.multiplier ^ 2) ∧
      ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E D.generator) ≫ ρ.map D.generator =
        (𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ (D.multiplier ^ 2) := by
  constructor
  · rw [← ρ.map_mul, mul_comm, D.norm, ← Nat.cast_pow, GeneratorIsogeny.integralAction_map_natCast]
  · rw [← ρ.map_mul, D.norm, ← Nat.cast_pow, GeneratorIsogeny.integralAction_map_natCast]

theorem GeneratorReconstruction.CMIntegralGeneratorData.action_isogeny (D : GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (hd : ∀ s : S, IsUnit (D.multiplier : S.presheaf.stalk s)) :
    IsFinite (ρ.map D.generator).left ∧ Etale (ρ.map D.generator).left ∧
      Surjective (ρ.map D.generator).left ∧
      ∀ (T : Over S) (x : T ⟶ A.scheme), x ≫ ρ.map D.generator = 1 →
        x ^ (D.multiplier ^ 2) = 1 := by
  obtain ⟨hfg, hgf⟩ := D.action_complements A ρ
  have hn (s : S) : IsUnit ((D.multiplier ^ 2 : ℕ) : S.presheaf.stalk s) := by
    simpa only [Nat.cast_pow] using (hd s).pow 2
  obtain ⟨hf, he, hs⟩ := UnitMultiplication.unit_multiplication_factor_finite_etale_surjective A.scheme
    (ρ.map D.generator) (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E D.generator))
    (D.multiplier ^ 2) hn hfg hgf
  refine ⟨hf, he, hs, ?_⟩
  intro T x hx
  calc
    x ^ (D.multiplier ^ 2) = x ≫ (𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ (D.multiplier ^ 2) := by
      rw [MonObj.comp_pow, Category.comp_id]
    _ = x ≫ (ρ.map D.generator ≫
        ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E D.generator)) := by rw [hfg]
    _ = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM
