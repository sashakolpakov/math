import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.TestReindex
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators

/-! # Test Reindex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.TestReindex.CM

noncomputable section

/-! Coordinate relabeling on the actual adelic Schwartz tensor span. -/

open scoped Classical
variable {I J : Type*} [Fintype I] [Fintype J]

theorem tensor_function (e : I ≃ J) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.pureTensor f φ ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.pureTensor (Real.TestReindex.CM.tests e f) (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e φ) := rfl

theorem mem (e : I ≃ J) (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) :
    F.val ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz J := by
  obtain ⟨F, hF⟩ := F
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, φ, rfl⟩ := hF
    rw [tensor_function]
    exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor _ _).property
  | zero => exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz J).zero_mem
  | add F G _ _ hF hG => exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz J).add_mem hF hG
  | smul c F _ hF => exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz J).smul_mem c hF

def tests (e : I ≃ J) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz J where
  toFun F := ⟨F.val ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm, CM.mem e F⟩
  invFun F := ⟨F.val ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e, by
    have h := CM.mem e.symm F
    exact h⟩
  left_inv F := by
    apply Subtype.ext
    funext x
    change F.val (fun i => x (e.symm (e i))) = F.val x
    simp only [e.symm_apply_apply]
  right_inv F := by
    apply Subtype.ext
    funext y
    change F.val (fun j => y (e (e.symm j))) = F.val y
    simp only [e.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tests_apply (e : I ≃ J) (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) (y : J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (tests e F).val y = F.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y) := rfl

theorem tests_symm_apply (e : I ≃ J) (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz J) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    ((tests e).symm F).val x = F.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x) := rfl

theorem tests_tensor (e : I ≃ J) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    tests e (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (Real.TestReindex.CM.tests e f) (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e φ) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.TestReindex.CM
