import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Heisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticProduct
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.AdelicPairGroup

/-! # Pair Intertwiner -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairIntertwiner.CM

noncomputable section

/-! Heisenberg covariance of the actual real–finite product action on
the complete adelic Schwartz tensor span. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.AdelicPairGroup.CM
variable (n : ℕ)
variable {MpR MpF : Type*} [Group MpR] [Group MpF]
variable {μ : Measure (Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)}
variable (R : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) MpR)
variable (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf Constructed.AdelicCharacter.CM.Finite.character μ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) MpF)

theorem real_covariance (r : MpR) (p q : Fin n → ℝ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) :
    R.action r (Real.Heisenberg.CM.operator n p q f) = Real.Heisenberg.CM.operator n
      (fun i => ((R.project r).val *ᵥ Sum.elim p q) (Sum.inl i))
      (fun i => ((R.project r).val *ᵥ Sum.elim p q) (Sum.inr i)) (R.action r f) := by
  apply Subtype.ext
  exact funext (R.intertwines r p q f (Real.Heisenberg.CM.operator n p q f) (fun _ => rfl))

theorem finite_covariance (f : MpF) (p q : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    F.action f (Finite.FourierHeisenberg.CM.operator p q φ) = Finite.FourierHeisenberg.CM.operator
      (fun i => ((F.project f).val *ᵥ Sum.elim p q) (Sum.inl i))
      (fun i => ((F.project f).val *ᵥ Sum.elim p q) (Sum.inr i)) (F.action f φ) := by
  apply Subtype.ext
  exact funext (F.intertwines f p q φ (Finite.FourierHeisenberg.CM.operator p q φ) (fun _ => rfl))

theorem operator_covariance (r : MpR) (f : MpF) (p q : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (AdelicPairGroup.CM.action R F (AdelicPairGroup.CM.assemble R F (r, f))).toLinearMap.comp (Heisenberg.CM.operator n p q) =
      (Heisenberg.CM.operator n
        (fun i => ((AdelicPairGroup.CM.projection R F (AdelicPairGroup.CM.assemble R F (r, f))).val *ᵥ Sum.elim p q) (Sum.inl i))
        (fun i => ((AdelicPairGroup.CM.projection R F (AdelicPairGroup.CM.assemble R F (r, f))).val *ᵥ Sum.elim p q) (Sum.inr i))).comp
          (AdelicPairGroup.CM.action R F (AdelicPairGroup.CM.assemble R F (r, f))).toLinearMap := by
  rw [AdelicPairGroup.CM.projection_assemble, AdelicPairGroup.CM.action_assemble]
  apply FiniteOperators.CM.Sections.linear_ext
  intro h φ
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    Heisenberg.CM.operator_tensor, ProductOperators.CM.operator_tensor]
  simp_rw [SymplecticProduct.CM.Phase.phase_fst, SymplecticProduct.CM.Phase.phase_snd]
  rw [real_covariance, finite_covariance]

theorem assemble_intertwines (r : MpR) (f : MpF) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg Constructed.AdelicCharacter.CM.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n))
      (AdelicPairGroup.CM.projection R F (AdelicPairGroup.CM.assemble R F (r, f))) (AdelicPairGroup.CM.action R F (AdelicPairGroup.CM.assemble R F (r, f))) := by
  intro p q Φ Ψ hΨ x
  have he : Ψ = Heisenberg.CM.operator n p q Φ := Subtype.ext (funext hΨ)
  rw [he]
  have h := LinearMap.congr_fun (operator_covariance n R F r f p q) Φ
  exact congrFun (congrArg Subtype.val h) x

theorem intertwines (a : AdelicPairGroup.CM.PairGroup R F) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.IntertwinesHeisenberg Constructed.AdelicCharacter.CM.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n))
      (AdelicPairGroup.CM.projection R F a) (AdelicPairGroup.CM.action R F a) := by
  obtain ⟨⟨r, f⟩, rfl⟩ := AdelicPairGroup.CM.assemble_surjective R F a
  exact assemble_intertwines n R F r f

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairIntertwiner.CM
