import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Test Reindex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.TestReindex.CM

noncomputable section

/-! Actual real Schwartz functions and Lebesgue measure under a
finite coordinate relabeling. -/

open scoped Classical
open _root_.MeasureTheory
variable {I J : Type*} [Fintype I] [Fintype J]

def coordinates (e : I ≃ J) : (I → ℝ) ≃L[ℝ] (J → ℝ) where
  toFun := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e
  invFun := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm
  left_inv x := by funext i; exact congrArg x (e.symm_apply_apply i)
  right_inv y := by funext j; exact congrArg y (e.apply_symm_apply j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e).continuous
  continuous_invFun := (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm).continuous

theorem mem (e : I ≃ J) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) :
    (f.val ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm) ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz J := by
  obtain ⟨φ, hφ⟩ := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff f.val).mp f.property
  refine (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff _).mpr
    ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (coordinates e.symm) φ, ?_⟩
  rw [hφ]
  rfl

def tests (e : I ≃ J) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz J where
  toFun f := ⟨f.val ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm, mem e f⟩
  invFun f := ⟨f.val ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e, by
    have h := mem e.symm f
    exact h⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change f.val (fun i => x (e.symm (e i))) = f.val x
    simp only [e.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    funext y
    change f.val (fun j => y (e (e.symm j))) = f.val y
    simp only [e.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tests_apply (e : I ≃ J) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (y : J → ℝ) :
    (tests e f).val y = f.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y) := rfl

theorem tests_symm_apply (e : I ≃ J) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz J) (x : I → ℝ) :
    ((tests e).symm f).val x = f.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x) := rfl

theorem measurePreserving (e : I ≃ J) :
    MeasurePreserving (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e (K := ℝ)) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : J => ℝ) e
  have he : (MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e : (I → ℝ) → (J → ℝ)) =
      RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e := by
    funext x j
    obtain ⟨i, rfl⟩ := e.surjective j
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    change x i = x (e.symm (e i))
    rw [e.symm_apply_apply]
  rwa [he] at h

theorem integral_reindex (e : I ≃ J) (f : (J → ℝ) → ℂ) :
    (∫ x, f (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x)) = ∫ y, f y :=
  (measurePreserving e).integral_comp (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e).measurableEmbedding f

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.TestReindex.CM
