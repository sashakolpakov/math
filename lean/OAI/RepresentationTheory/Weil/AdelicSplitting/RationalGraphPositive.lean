import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaFourierPositive
import OAI.RepresentationTheory.Weil.AdelicSplitting.PositiveScalarProduct
import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalFourier

/-! # Rational Graph Positive -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RationalGraphPositive.Construction

noncomputable section

/-! Adelic Poisson positivity eliminates the scalar identity fiber of
the actual rational generator graph, yielding its rational homomorphism. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.MeasureTheory

section

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
variable (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)
variable (hn : ∀ v : InfinitePlace F, ∃ t : v.Completion, Characters.Construction.localAdditiveCharacter F ψ (.inl v) t ≠ 1)
variable (hμ : ∀ v : ArchimedeanAdeles.Construction.Places F,
  (Local.FunctionsMetaplectic.Construction.positionMeasure (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v)).IsAddHaarMeasure)

include hc hu hp hn hμ in
theorem rationalGraph_positive :
    Rational.Construction.rationalGraph F N ψ ≤ (PositiveScalarProduct.Construction.globalPositiveThetaSubgroup F N ψ).comap (MonoidHom.snd _ _) := by
  change Subgroup.closure (Rational.Construction.rationalGeneratorPairs F N ψ) ≤ _
  apply (Subgroup.closure_le ((PositiveScalarProduct.Construction.globalPositiveThetaSubgroup F N ψ).comap
    (MonoidHom.snd (Local.FunctionsMetaplectic.Construction.Symplectic F N) (Vacuum.Construction.GlobalCover F N ψ)))).mpr
  intro z hz
  rcases hz with ⟨A, a, ha, rfl⟩ | ⟨B, a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · exact PositiveScalarProduct.Construction.rationalLevi_globalPositiveTheta F N ψ A a ha
  · exact PositiveScalarProduct.Construction.rationalQuadratic_globalPositiveTheta F N ψ hc hp B a ha
  · exact ⟨a, ThetaFourierPositive.Construction.rationalFourier_mem_positiveThetaSubgroup F N ψ hc hu hp hn
      (fun v => hμ (.inr v)) (fun v => hμ (.inl v)) a ha, rfl⟩

end

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (hN : 0 < n * m)
  (H : (Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))ˣ)
  (C : Characters.Construction.GlobalCharacters F d n m) (P : Assembly.Construction.GlobalFrames F d n m H K)
  (D : Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

include hN D in
theorem normalized_rationalGraph_positive :
    Rational.Construction.rationalGraph F (n * m) C.ψ ≤
      (PositiveScalarProduct.Construction.globalPositiveThetaSubgroup F (n * m) C.ψ).comap (MonoidHom.snd _ _) := by
  apply rationalGraph_positive F (n * m) C.ψ C.ψ_continuous C.ψ_unitary C.ψ_principal
  · intro v
    exact NontrivialLocalCharacter.Construction.normalizedLocalSplittings_character_nontrivial F d hd n m hN H K C P D (.inl v)
  · intro v
    let : (Local.FunctionsMetaplectic.Construction.selfDualMeasure (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)).IsAddHaarMeasure :=
      NormalizationNonvanishing.Construction.normalized_selfDualMeasure_isAddHaarMeasure F d hd n m H K C P D v hN
    unfold Local.FunctionsMetaplectic.Construction.positionMeasure
    infer_instance

include hN D in
theorem normalized_rationalGraph_identity_fiber (a : Vacuum.Construction.GlobalCover F (n * m) C.ψ)
    (ha : (1, a) ∈ Rational.Construction.rationalGraph F (n * m) C.ψ) : a = 1 := by
  let w : ArchimedeanAdeles.Construction.Places F := .inl (Classical.choice (inferInstance : Nonempty (InfinitePlace F)))
  exact PositiveScalarProduct.Construction.globalPositiveTheta_scalar_eq_one F (n * m) C.ψ w a
    (normalized_rationalGraph_positive F d hd n m hN H K C P D ha)
    (GlobalKernel.Construction.rationalGraph_identity_is_scalar F d hd n m hN H K C P D w a ha)

include hN D in
theorem normalized_rationalGraph_realization (hns : ¬ IsSquare d)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val) :
    ∃ r : Local.FunctionsMetaplectic.Construction.Symplectic F (n * m) →* Vacuum.Construction.GlobalCover F (n * m) C.ψ,
      (∀ γ a, (γ, a) ∈ Rational.Construction.rationalGraph F (n * m) C.ψ ↔ r γ = a) ∧
      ∀ γ, Vacuum.Construction.globalProjection F (n * m) C.ψ (r γ) = Vacuum.Construction.rationalSymplectic F (n * m) γ :=
  GraphReduction.Construction.rationalGraph_realization_of_total_and_identity_fiber F (n * m) C.ψ
    (RationalFourier.Construction.normalized_rationalGraph_total F d hd hns n m hN H K hH hK C P D)
    (normalized_rationalGraph_identity_fiber F d hd n m hN H K C P D)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RationalGraphPositive.Construction
