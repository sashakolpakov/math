import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ProductOperators
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticProduct
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Adelic Pair Group -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.AdelicPairGroup.CM

noncomputable section

/-! The real–finite central-product candidate is an actual subgroup of
symplectic matrices paired with adelic Schwartz automorphisms. -/

open scoped Classical
open _root_.MeasureTheory
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {MpR MpF : Type*} [Group MpR] [Group MpF]
variable {ψ : AddChar RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ℂ} {μ : Measure (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)}
variable (R : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) MpR)
variable (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ψ μ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) MpF)

def pairHom : (MpR × MpF) →* (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ × (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I)) :=
  (SymplecticProduct.CM.pair.comp (R.project.prodMap F.project)).prod
    (ProductOperators.CM.operator.comp (R.action.prodMap F.action))

abbrev PairGroup := (pairHom R F).range

def assemble : (MpR × MpF) →* PairGroup R F := (pairHom R F).rangeRestrict

def projection : PairGroup R F →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ :=
  (MonoidHom.fst _ _).comp (pairHom R F).range.subtype

def action : PairGroup R F →* (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :=
  (MonoidHom.snd _ _).comp (pairHom R F).range.subtype

def includeReal : MpR →* PairGroup R F := (assemble R F).comp (MonoidHom.inl MpR MpF)
def includeFinite : MpF →* PairGroup R F := (assemble R F).comp (MonoidHom.inr MpR MpF)

theorem assemble_surjective : Function.Surjective (assemble R F) :=
  (pairHom R F).rangeRestrict_surjective

theorem projection_assemble (r : MpR) (f : MpF) :
    projection R F (assemble R F (r, f)) = SymplecticProduct.CM.pair (R.project r, F.project f) := rfl

theorem action_assemble (r : MpR) (f : MpF) :
    CM.action R F (assemble R F (r, f)) = ProductOperators.CM.operator (R.action r, F.action f) := rfl

theorem include_product (r : MpR) (f : MpF) :
    includeReal R F r * includeFinite R F f = assemble R F (r, f) := by
  change assemble R F (r, 1) * assemble R F (1, f) = _
  rw [← map_mul]
  congr 1
  exact Prod.ext (mul_one r) (one_mul f)

theorem includes_commute (r : MpR) (f : MpF) :
    Commute (includeReal R F r) (includeFinite R F f) := by
  have h : Commute ((r, 1) : MpR × MpF) (1, f) := by
    apply Prod.ext <;> simp
  exact h.map (assemble R F)

theorem factorization (r : MpR) (f : MpF) (h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    CM.action R F (includeReal R F r * includeFinite R F f) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h φ) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (R.action r h) (F.action f φ) := by
  rw [include_product, action_assemble]
  exact ProductOperators.CM.operator_tensor _ _ h φ

theorem faithful : Function.Injective (fun a : PairGroup R F => (projection R F a, CM.action R F a)) := by
  intro a b h
  exact Subtype.ext h

theorem projection_surjective : Function.Surjective (projection R F) := by
  intro g
  obtain ⟨r, hr⟩ := R.surjective (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) g)
  obtain ⟨f, hf⟩ := F.surjective (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) g)
  refine ⟨assemble R F (r, f), ?_⟩
  rw [projection_assemble, hr, hf]
  exact SymplecticProduct.CM.pair_projections g

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.AdelicPairGroup.CM
