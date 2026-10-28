import OAI.LieTheory.Semisimple.CharacterTrivialityKills
import OAI.LieTheory.Semisimple.Regularity
import Lean.Util.CollectAxioms

/-! # Character Triviality Eq -/

namespace OAI.LieTheory.Semisimple.CharacterTrivialityEq.Constructions

noncomputable section

/-!
# CharacterTriviality: continuous characters of connected semisimple real Lie groups

The hypotheses match `Statements/CharacterTriviality.lean`, which is not imported. The helper
instance `realLieGroupMinSmoothness` supplies the canonical Lie algebra instance
without adding a mathematical hypothesis. Compact smoothing with Haar measure
gives automatic smoothness; differentiation, semisimplicity, and connectedness
then give triviality.
-/

open scoped _root_.Manifold ContDiff

/-- A Lie-group character on a connected semisimple group is trivial. -/
theorem continuous_character_eq_one
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (G : Type*) [Group G] [TopologicalSpace G]
    [T2Space G] [SecondCountableTopology G] [ConnectedSpace G]
    [ChartedSpace E G]
    [LieGroup (𝓘(ℝ, E)) ∞ G]
    [LieAlgebra.IsSemisimple ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)]
    (χ : ContinuousMonoidHom G Circle) :
    ∀ g : G, χ g = 1 := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace (H := E) (M := G)
  let φ : G →* ℂ := Circle.coeHom.comp χ.toMonoidHom
  have hφ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ φ :=
    Regularity.Constructions.CharacterTriviality.contMDiff_character (E := E) (μ := MeasureTheory.Measure.haar) χ
  have hd1v : mvfderiv (𝓘(ℝ, E)) φ 1 = 0 := by
    have hlin := Algebra.Constructions.CharacterTriviality.linearMap_eq_zero_of_brackets
      (mvfderiv (𝓘(ℝ, E)) φ 1).toLinearMap
      (CharacterTrivialityKills.Constructions.character_derivative_kills_brackets φ hφ)
    ext v
    exact congrArg (fun f : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ[ℝ] ℂ => f v) hlin
  have hd1 : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) φ 1 = 0 := by
    convert! hd1v
  have hd (g : G) : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) φ g = 0 := by
    let A : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) (φ g)
    let l : G → G := fun y => g⁻¹ * y
    have hl : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) l g :=
      (contMDiff_mul_left (n := ∞)).mdifferentiableAt (by simp)
    have hcomp : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) (φ ∘ l) g :=
      (hφ.mdifferentiable (by simp) (l g)).comp g hl
    have hzero : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) (φ ∘ l) g = 0 := by
      rw [mfderiv_comp g (hφ.mdifferentiable (by simp) _) hl]
      change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) φ (g⁻¹ * g)).comp _ = _
      rw [inv_mul_cancel, hd1]
      rfl
    have heq : (φ : G → ℂ) = A ∘ (φ ∘ l) := by
      funext y
      change φ y = φ g * φ (g⁻¹ * y)
      rw [← φ.map_mul, mul_inv_cancel_left]
    rw [heq, mfderiv_comp g A.differentiable.differentiableAt.mdifferentiableAt hcomp, hzero]
    exact ContinuousLinearMap.comp_zero _
  intro g
  apply Circle.ext
  have hconst := Differential.Constructions.CharacterTriviality.eq_of_mfderiv_zero (hφ.mdifferentiable (by simp)) hd g (1 : G)
  change φ g = 1
  exact hconst.trans φ.map_one

end

end OAI.LieTheory.Semisimple.CharacterTrivialityEq.Constructions
