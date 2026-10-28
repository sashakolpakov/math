import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.AdelicPairGroup
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.RealFaithful

/-! # Pair Decomposition -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairDecomposition.CM.Kernel

/-! Exact two-fold kernel and the diagonal-sign central-product
relation for the actual adelic pair group. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.AdelicPairGroup.CM
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {MpR MpF : Type*} [Group MpR] [Group MpF]
variable {ψ : AddChar RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ℂ} {μ : Measure (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)}
variable (R : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) MpR)
variable (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ψ μ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) MpF)

theorem real_neg : R.action R.negOne = LinearEquiv.neg ℂ := LinearEquiv.ext R.genuine
theorem finite_neg : F.action F.negOne = LinearEquiv.neg ℂ := LinearEquiv.ext F.genuine

def negOne : AdelicPairGroup.CM.PairGroup R F := AdelicPairGroup.CM.assemble R F (R.negOne, 1)

theorem project_negOne : AdelicPairGroup.CM.projection R F (Kernel.negOne R F) = 1 := by
  rw [Kernel.negOne, AdelicPairGroup.CM.projection_assemble, R.project_negOne, map_one]
  exact SymplecticProduct.CM.pair.map_one

theorem action_negOne : AdelicPairGroup.CM.action R F (Kernel.negOne R F) = LinearEquiv.neg ℂ := by
  rw [Kernel.negOne, AdelicPairGroup.CM.action_assemble, real_neg, map_one]
  change RealOperators.CM.operator (LinearEquiv.neg ℂ) *
    FiniteOperators.CM.operator 1 = _
  rw [ProductOperators.CM.real_neg, map_one, mul_one]

theorem negOne_ne_one : Kernel.negOne R F ≠ 1 := by
  intro he
  have ha := congrArg (AdelicPairGroup.CM.action R F) he
  rw [action_negOne, map_one] at ha
  have hr : R.action R.negOne = 1 := by
    apply RealFaithful.CM.operator_injective
    rw [real_neg, ProductOperators.CM.real_neg, map_one]
    exact ha
  apply R.negOne_ne_one
  apply R.faithful
  apply Prod.ext
  · exact R.project_negOne.trans R.project.map_one.symm
  · exact hr.trans R.action.map_one.symm

theorem assemble_neg_neg : AdelicPairGroup.CM.assemble R F (R.negOne, F.negOne) = 1 := by
  apply AdelicPairGroup.CM.faithful R F
  change (AdelicPairGroup.CM.projection R F (AdelicPairGroup.CM.assemble R F (R.negOne, F.negOne)),
    AdelicPairGroup.CM.action R F (AdelicPairGroup.CM.assemble R F (R.negOne, F.negOne))) = (AdelicPairGroup.CM.projection R F 1, AdelicPairGroup.CM.action R F 1)
  rw [AdelicPairGroup.CM.projection_assemble, AdelicPairGroup.CM.action_assemble, R.project_negOne, F.project_negOne,
    real_neg, finite_neg, ProductOperators.CM.neg_neg, map_one, map_one]
  exact Prod.ext SymplecticProduct.CM.pair.map_one rfl

theorem assemble_one_neg : AdelicPairGroup.CM.assemble R F (1, F.negOne) = Kernel.negOne R F := by
  apply AdelicPairGroup.CM.faithful R F
  change (AdelicPairGroup.CM.projection R F (AdelicPairGroup.CM.assemble R F (1, F.negOne)),
    AdelicPairGroup.CM.action R F (AdelicPairGroup.CM.assemble R F (1, F.negOne))) = (AdelicPairGroup.CM.projection R F (Kernel.negOne R F), AdelicPairGroup.CM.action R F (Kernel.negOne R F))
  rw [Kernel.project_negOne, action_negOne, AdelicPairGroup.CM.projection_assemble, AdelicPairGroup.CM.action_assemble,
    map_one, map_one, F.project_negOne, finite_neg]
  apply Prod.ext
  · exact SymplecticProduct.CM.pair.map_one
  · change RealOperators.CM.operator 1 * FiniteOperators.CM.operator (LinearEquiv.neg ℂ) = _
    rw [map_one, one_mul, ProductOperators.CM.finite_neg]

theorem kernel (a : AdelicPairGroup.CM.PairGroup R F) : AdelicPairGroup.CM.projection R F a = 1 ↔ a = 1 ∨ a = Kernel.negOne R F := by
  constructor
  · intro ha
    obtain ⟨⟨r, f⟩, rfl⟩ := AdelicPairGroup.CM.assemble_surjective R F a
    rw [AdelicPairGroup.CM.projection_assemble, SymplecticProduct.CM.pair_eq_one] at ha
    rcases (R.kernel r).mp ha.1 with rfl | rfl
    · rcases (F.kernel f).mp ha.2 with rfl | rfl
      · exact Or.inl (AdelicPairGroup.CM.assemble R F).map_one
      · exact Or.inr (assemble_one_neg R F)
    · rcases (F.kernel f).mp ha.2 with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (assemble_neg_neg R F)
  · rintro (rfl | rfl)
    · exact map_one _
    · exact Kernel.project_negOne R F

theorem centralProduct_kernel (r : MpR) (f : MpF) :
    AdelicPairGroup.CM.includeReal R F r * AdelicPairGroup.CM.includeFinite R F f = 1 ↔
      (r = 1 ∧ f = 1) ∨ (r = R.negOne ∧ f = F.negOne) := by
  rw [AdelicPairGroup.CM.include_product]
  constructor
  · intro he
    have hp := congrArg (AdelicPairGroup.CM.projection R F) he
    rw [AdelicPairGroup.CM.projection_assemble, map_one, SymplecticProduct.CM.pair_eq_one] at hp
    rcases (R.kernel r).mp hp.1 with rfl | rfl
    · rcases (F.kernel f).mp hp.2 with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (Kernel.negOne_ne_one R F ((assemble_one_neg R F).symm.trans he))
    · rcases (F.kernel f).mp hp.2 with rfl | rfl
      · exact False.elim (Kernel.negOne_ne_one R F he)
      · exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact (AdelicPairGroup.CM.assemble R F).map_one
    · exact assemble_neg_neg R F

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairDecomposition.CM.Kernel

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairDecomposition.CM

/-! Exact real–finite decomposition of the concrete adelic pair group,
with the prescribed real lift held fixed. -/

open scoped Classical _root_.Matrix
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.AdelicPairGroup.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairDecomposition.CM.Kernel
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {MpR MpF : Type*} [Group MpR] [Group MpF]
variable {ψ : AddChar RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ℂ} {μ : Measure (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)}
variable (R : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) MpR)
variable (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ψ μ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) MpF)

theorem includeReal_covers (r : MpR) :
    (AdelicPairGroup.CM.projection R F (AdelicPairGroup.CM.includeReal R F r)).val = fun i j =>
      ((R.project r).val i j, (1 : Matrix (Sum I I) (Sum I I) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) i j) := by
  change (AdelicPairGroup.CM.projection R F (AdelicPairGroup.CM.assemble R F (r, 1))).val = _
  rw [AdelicPairGroup.CM.projection_assemble, map_one]
  rfl

theorem includeFinite_covers (f : MpF) :
    (AdelicPairGroup.CM.projection R F (AdelicPairGroup.CM.includeFinite R F f)).val = fun i j =>
      ((1 : Matrix (Sum I I) (Sum I I) ℝ) i j, (F.project f).val i j) := by
  change (AdelicPairGroup.CM.projection R F (AdelicPairGroup.CM.assemble R F (1, f))).val = _
  rw [AdelicPairGroup.CM.projection_assemble, map_one]
  rfl

theorem include_signs : AdelicPairGroup.CM.includeReal R F R.negOne = AdelicPairGroup.CM.includeFinite R F F.negOne :=
  (Kernel.assemble_one_neg R F).symm

theorem decompose (a : AdelicPairGroup.CM.PairGroup R F) (r : MpR)
    (ha : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (AdelicPairGroup.CM.projection R F a) = R.project r) :
    ∃ f : MpF, AdelicPairGroup.CM.includeReal R F r * AdelicPairGroup.CM.includeFinite R F f = a := by
  obtain ⟨⟨s, f⟩, rfl⟩ := AdelicPairGroup.CM.assemble_surjective R F a
  rw [AdelicPairGroup.CM.projection_assemble, SymplecticProduct.CM.pair_fst] at ha
  have hp : R.project (r⁻¹ * s) = 1 := by
    rw [map_mul, map_inv, ha, inv_mul_cancel]
  rcases (R.kernel (r⁻¹ * s)).mp hp with h | h
  · have hs : s = r := by
      have hh := congrArg (fun t : MpR => r * t) h
      simpa only [mul_inv_cancel_left, mul_one] using hh
    subst s
    exact ⟨f, AdelicPairGroup.CM.include_product R F r f⟩
  · have hs : s = r * R.negOne := by
      have hh := congrArg (fun t : MpR => r * t) h
      simpa only [mul_inv_cancel_left] using hh
    refine ⟨F.negOne * f, ?_⟩
    rw [hs, ← AdelicPairGroup.CM.include_product, map_mul, map_mul, include_signs, mul_assoc]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairDecomposition.CM

end

end OAI
