import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.GeneratorIsogeny
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions

/-! # Action Generator Faithfulness -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel

/-! The constructed primitive isogeny determines the entire integral
CM action. Cancellation is proved geometrically over the arithmetic base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open _root_.Polynomial

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.integral_reconstruction (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    (a : NumberField.RingOfIntegers E) :
    aeval D.generator (D.polynomial a) = (D.conductor : NumberField.RingOfIntegers E) * a := by
  apply NumberField.RingOfIntegers.coe_injective
  have h := aeval_algHom_apply (algebraMap (NumberField.RingOfIntegers E) E).toIntAlgHom
    D.generator (D.polynomial a)
  exact h.symm.trans (D.reconstruction a)

theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.ring_action_eq_of_generator (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {R : Type*} [Ring R] (ρ σ : NumberField.RingOfIntegers E →+* R)
    (hc : Function.Injective (fun r : R => (D.conductor : R) * r))
    (hv : ρ D.generator = σ D.generator) : ρ = σ := by
  apply RingHom.ext
  intro a
  apply hc
  have hρ : (D.conductor : R) * ρ a = aeval (ρ D.generator) (D.polynomial a) := by
    have he : aeval (ρ D.generator) (D.polynomial a) = ρ (aeval D.generator (D.polynomial a)) :=
      aeval_algHom_apply ρ.toIntAlgHom D.generator (D.polynomial a)
    rw [D.integral_reconstruction, map_mul, map_natCast] at he
    exact he.symm
  have hσ : (D.conductor : R) * σ a = aeval (σ D.generator) (D.polynomial a) := by
    have he : aeval (σ D.generator) (D.polynomial a) = σ (aeval D.generator (D.polynomial a)) :=
      aeval_algHom_apply σ.toIntAlgHom D.generator (D.polynomial a)
    rw [D.integral_reconstruction, map_mul, map_natCast] at he
    exact he.symm
  exact hρ.trans ((congrArg (fun x => aeval x (D.polynomial a)) hv).trans hσ.symm)

theorem Finite.Actions.GroupEndRing.hom_natCast {S : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (n : ℕ) :
    (n : Finite.Actions.GroupEndRing A).hom A = (𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n := by
  induction n with
  | zero => simp only [Nat.cast_zero, Finite.Actions.GroupEndRing.hom_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, Finite.Actions.GroupEndRing.hom_add, ih, Finite.Actions.GroupEndRing.hom_one, pow_succ]

theorem Finite.Actions.GroupEndRing.unit_natCast_mul_injective {S : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (n : ℕ)
    (hn : ∀ s : S, IsUnit (n : S.presheaf.stalk s)) :
    Function.Injective (fun r : Finite.Actions.GroupEndRing A => (n : Finite.Actions.GroupEndRing A) * r) := by
  obtain ⟨hf, he, _⟩ := UnitMultiplication.unit_multiplication_finite_etale_surjective A.scheme n hn
  let q : A.scheme ⟶ A.scheme := (𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n
  have : IsFinite q.left := hf
  have : Etale q.left := he
  intro r t h
  have hc := congrArg (fun v : Finite.Actions.GroupEndRing A => (v.hom A).left) h
  simp only [Finite.Actions.GroupEndRing.hom_mul, Finite.Actions.GroupEndRing.hom_natCast, Over.comp_left] at hc
  apply Finite.Actions.GroupEndRing.ext
  apply Over.OverMorphism.ext
  apply Relative.PointedLifts.relative_pointed_unramified_lifts_unique A.scheme.hom η[A.scheme].left η[A.scheme].w
    q.left (r.hom A).left (t.hom A).left hc
  exact congrArg Over.Hom.left ((IsMonHom.one_hom (r.hom A)).trans
    (IsMonHom.one_hom (t.hom A)).symm)

theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.integral_action_eq_of_generator (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (hc : ∀ s : S, IsUnit (D.conductor : S.presheaf.stalk s))
    (hv : ρ.map D.generator = σ.map D.generator) : ρ = σ := by
  have h := D.ring_action_eq_of_generator (Finite.Actions.ringHomOfIntegralAction A ρ) (Finite.Actions.ringHomOfIntegralAction A σ)
    (Finite.Actions.GroupEndRing.unit_natCast_mul_injective A D.conductor hc) (Finite.Actions.GroupEndRing.ext A hv)
  apply Finite.Actions.integralAction_ext A
  intro a
  exact congrArg (fun v : Finite.Actions.GroupEndRing A => v.hom A) (RingHom.congr_fun h a)

end AlgebraicGeometry.PELModuli.IntegralModel

namespace AlgebraicGeometry.PELModuli.IntegralModel.CM

/-! Rosati conjugation turns the constructed primitive CM isogeny into
a polarized similitude with the fixed rational-square multiplier. The
actual dual map and its Poincare comparison are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem GeneratorReconstruction.CMIntegralGeneratorData.rosati_similitude (D : GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) :
    ∃ q : A.dual.abelian.scheme ⟶ A.dual.abelian.scheme,
      IsMonHom q ∧
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 A.abelian.scheme).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 A.dual.abelian.scheme ⊗ₘ ρ.map D.generator).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) ∧
      ρ.map D.generator ≫ A.polarization.isogeny.hom ≫ q =
        ((𝟙 A.abelian.scheme : A.abelian.scheme ⟶ A.abelian.scheme) ^ (D.multiplier ^ 2)) ≫
          A.polarization.isogeny.hom := by
  obtain ⟨q, hq, hPoincare, hPolarization⟩ := hρ D.generator
  refine ⟨q, hq, hPoincare, ?_⟩
  have hc : ρ.map D.generator ≫
      ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E D.generator) =
        (𝟙 A.abelian.scheme : A.abelian.scheme ⟶ A.abelian.scheme) ^ (D.multiplier ^ 2) :=
    (D.action_complements A.abelian ρ).1
  rw [hPolarization, ← Category.assoc]
  exact congrArg (fun f : A.abelian.scheme ⟶ A.abelian.scheme => f ≫ A.polarization.isogeny.hom) hc

end AlgebraicGeometry.PELModuli.IntegralModel.CM

end

end OAI
