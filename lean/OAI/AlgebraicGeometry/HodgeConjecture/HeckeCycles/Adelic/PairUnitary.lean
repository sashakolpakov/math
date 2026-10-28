import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Pairing
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.AdelicPairGroup

/-! # Pair Unitary -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairUnitary.CM

noncomputable section

/-! Unitarity of the actual adelic product action, first on pure tensors
and then on their full finite linear span. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Pairing.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.AdelicPairGroup.CM
variable {I : Type*} [Fintype I]
variable (μ : Measure (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) [μ.IsAddHaarMeasure]

theorem unitary_of_tensors (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I)
    (hU : ∀ (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ η : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I),
      Pairing.CM.pairing μ (U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ)) (U (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h η)) = Pairing.CM.pairing μ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h η))
    (F G : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) : Pairing.CM.pairing μ (U F) (U G) = Pairing.CM.pairing μ F G := by
  refine Submodule.span_induction₂
    (p := fun f g hf hg => Pairing.CM.pairing μ (U ⟨f, hf⟩) (U ⟨g, hg⟩) = Pairing.CM.pairing μ ⟨f, hf⟩ ⟨g, hg⟩)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ F.property G.property
  · intro f g hf hg
    obtain ⟨f, φ, rfl⟩ := hf
    obtain ⟨h, η, rfl⟩ := hg
    exact hU f h φ η
  · intro g hg
    change Pairing.CM.pairing μ (U 0) (U ⟨g, hg⟩) = Pairing.CM.pairing μ 0 ⟨g, hg⟩
    rw [map_zero, Pairing.CM.zero_left, Pairing.CM.zero_left]
  · intro f hf
    change Pairing.CM.pairing μ (U ⟨f, hf⟩) (U 0) = Pairing.CM.pairing μ ⟨f, hf⟩ 0
    rw [map_zero, Pairing.CM.zero_right, Pairing.CM.zero_right]
  · intro f g h hf hg hh ihf ihg
    change Pairing.CM.pairing μ (U (⟨f, hf⟩ + ⟨g, hg⟩)) (U ⟨h, hh⟩) = Pairing.CM.pairing μ (⟨f, hf⟩ + ⟨g, hg⟩) ⟨h, hh⟩
    rw [map_add, Pairing.CM.add_left, Pairing.CM.add_left, ihf, ihg]
  · intro f g h hf hg hh ihg ihh
    change Pairing.CM.pairing μ (U ⟨f, hf⟩) (U (⟨g, hg⟩ + ⟨h, hh⟩)) = Pairing.CM.pairing μ ⟨f, hf⟩ (⟨g, hg⟩ + ⟨h, hh⟩)
    rw [map_add, Pairing.CM.add_right, Pairing.CM.add_right, ihg, ihh]
  · intro c f g hf hg ih
    change Pairing.CM.pairing μ (U (c • ⟨f, hf⟩)) (U ⟨g, hg⟩) = Pairing.CM.pairing μ (c • ⟨f, hf⟩) ⟨g, hg⟩
    rw [map_smul, Pairing.CM.smul_left, Pairing.CM.smul_left, ih]
  · intro c f g hf hg ih
    change Pairing.CM.pairing μ (U ⟨f, hf⟩) (U (c • ⟨g, hg⟩)) = Pairing.CM.pairing μ ⟨f, hf⟩ (c • ⟨g, hg⟩)
    rw [map_smul, Pairing.CM.smul_right, Pairing.CM.smul_right, ih]

variable [DecidableEq I]
variable {MpR MpF : Type*} [Group MpR] [Group MpF] {ψ : AddChar RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ℂ}
variable (R : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) MpR)
variable (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ψ μ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) MpF)

theorem assemble_unitary (r : MpR) (f : MpF) (Φ Ψ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    Pairing.CM.pairing μ (AdelicPairGroup.CM.action R F (AdelicPairGroup.CM.assemble R F (r, f)) Φ) (AdelicPairGroup.CM.action R F (AdelicPairGroup.CM.assemble R F (r, f)) Ψ) = Pairing.CM.pairing μ Φ Ψ := by
  apply unitary_of_tensors μ
  intro h k φ η
  rw [AdelicPairGroup.CM.action_assemble, ProductOperators.CM.operator_tensor,
    ProductOperators.CM.operator_tensor, Pairing.CM.tensor_pairing, Pairing.CM.tensor_pairing,
    R.unitary, F.unitary]

theorem unitary (a : AdelicPairGroup.CM.PairGroup R F) (Φ Ψ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    (∫ x, (AdelicPairGroup.CM.action R F a Φ).val x * star ((AdelicPairGroup.CM.action R F a Ψ).val x) ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ) =
      ∫ x, Φ.val x * star (Ψ.val x) ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ := by
  obtain ⟨⟨r, f⟩, rfl⟩ := AdelicPairGroup.CM.assemble_surjective R F a
  exact assemble_unitary μ R F r f Φ Ψ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.PairUnitary.CM
