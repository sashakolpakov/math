import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.HilbertSchmidt
import OAI.NumberTheory.ArithmeticGroups.Lattices.StationaryStabilizerAdjoint
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Euclidean Representation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.EuclideanRepresentation.Construction

noncomputable section

section

/-! In Euclidean coordinates, the infinitesimal bracket representation
commutes with taking adjoints. -/

open _root_.ContinuousLinearMap

variable {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L] [Fintype ι]

local instance euclideanRepEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance euclideanRepEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance euclideanRepBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance euclideanRepBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance

def euclideanBracketRepresentation (b : OrthonormalBasis ι ℝ L) :
    (L →L[ℝ] L) →ₗ[ℝ]
      (EuclideanSpace ℝ (ι × ι × ι) →L[ℝ] EuclideanSpace ℝ (ι × ι × ι)) :=
  (Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis).conjContinuousAlgEquiv.toAlgEquiv.toLinearMap.comp
    ContinuousBracketRepresentation.Construction.continuousBracketRepresentation

theorem euclideanBracketRepresentation_apply (b : OrthonormalBasis ι ℝ L)
    (A : L →L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    euclideanBracketRepresentation b A (Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis B) =
      Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A) := by
  change Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis
    (ContinuousBracketRepresentation.Construction.continuousBracketRepresentation A ((Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis).symm
      (Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis B))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousBracketRepresentation.Construction.continuousBracketRepresentation_apply]

theorem euclideanBracketRepresentation_commutator (b : OrthonormalBasis ι ℝ L)
    (A C : L →L[ℝ] L) :
    euclideanBracketRepresentation b (A * C - C * A) =
      euclideanBracketRepresentation b A * euclideanBracketRepresentation b C -
        euclideanBracketRepresentation b C * euclideanBracketRepresentation b A := by
  change (Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis).conjContinuousAlgEquiv
    (ContinuousBracketRepresentation.Construction.continuousBracketRepresentation (A * C - C * A)) = _
  rw [ContinuousBracketRepresentation.Construction.continuousBracketRepresentation_commutator, map_sub, map_mul, map_mul]
  rfl

theorem euclideanBracketRepresentation_inner [CompleteSpace L] (b : OrthonormalBasis ι ℝ L)
    (A : L →L[ℝ] L) (B C : L →L[ℝ] L →L[ℝ] L) :
    inner ℝ (euclideanBracketRepresentation b A (Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis B))
      (Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis C) =
        inner ℝ (Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis B)
          (euclideanBracketRepresentation b (adjoint A) (Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis C)) := by
  rw [euclideanBracketRepresentation_apply, euclideanBracketRepresentation_apply,
    Bilinear.HilbertSchmidt.Construction.continuousBilinearEuclideanCoordinates_inner, Bilinear.HilbertSchmidt.Construction.continuousBilinearEuclideanCoordinates_inner]
  exact Bilinear.HilbertSchmidt.Construction.bilinear_derivationDefect_sum_inner b A B C

theorem euclideanBracketRepresentation_adjoint [CompleteSpace L] (b : OrthonormalBasis ι ℝ L)
    (A : L →L[ℝ] L) :
    euclideanBracketRepresentation b (adjoint A) = adjoint (euclideanBracketRepresentation b A) := by
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  obtain ⟨B, rfl⟩ := (Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis).surjective x
  obtain ⟨C, rfl⟩ := (Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis).surjective y
  simpa only [adjoint_adjoint] using euclideanBracketRepresentation_inner b (adjoint A) B C

end

/-! A minimum-norm representative of a nondegenerate Killing bracket
has a derivation algebra closed under taking adjoints. -/

open _root_.ContinuousLinearMap

variable {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L] [Fintype ι]

theorem minimum_bracket_derivation_adjoint [CompleteSpace L]
    (b : OrthonormalBasis ι ℝ L) (B : L →L[ℝ] L →L[ℝ] L)
    (hmin : ∀ e : L ≃L[ℝ] L, |LinearMap.det e.toLinearMap| = 1 →
      ‖Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis B‖ ≤
        ‖Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis (ContinuousBracketChange.Construction.continuousBracketChange e B)‖)
    (A : L →L[ℝ] L) (hA : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0) :
    Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint A) = 0 := by
  let Φ := Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis
  have hstat (T : L →L[ℝ] L) (hT : LinearMap.trace ℝ L T.toLinearMap = 0) :
      inner ℝ (euclideanBracketRepresentation b T (Φ B)) (Φ B) = 0 := by
    rw [euclideanBracketRepresentation_apply]
    exact MinimumStationary.Construction.minimum_bracket_orthogonal_to_traceless_change Φ.toContinuousLinearMap B hmin T hT
  have ha : euclideanBracketRepresentation b A (Φ B) = 0 := by
    rw [euclideanBracketRepresentation_apply, hA, map_zero]
  have h := StationaryStabilizerAdjoint.Construction.stationary_stabilizer_adjoint (euclideanBracketRepresentation b)
    (euclideanBracketRepresentation_commutator b) (euclideanBracketRepresentation_adjoint b)
    (Φ B) hstat A ha
  rw [euclideanBracketRepresentation_apply] at h
  apply Φ.injective
  simpa only [map_zero] using h

theorem exists_killing_bracket_with_adjoint_stable_derivations
    (b : OrthonormalBasis ι ℝ L) (B : L →L[ℝ] L →L[ℝ] L)
    (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ e : L ≃L[ℝ] L, |LinearMap.det e.toLinearMap| = 1 ∧
      ∀ A : L →L[ℝ] L, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect (ContinuousBracketChange.Construction.continuousBracketChange e B) A = 0 →
        Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect (ContinuousBracketChange.Construction.continuousBracketChange e B) (adjoint A) = 0 := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let Φ := Bilinear.EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis
  obtain ⟨e, he, hmin⟩ := OrbitMinimum.Construction.killing_bracket_orbit_has_minimum Φ B hB hK
  refine ⟨e, he, fun A hA => minimum_bracket_derivation_adjoint b (ContinuousBracketChange.Construction.continuousBracketChange e B) ?_ A hA⟩
  intro f hf
  rw [OrbitMinimum.Construction.continuousBracketChange_trans]
  exact hmin (e.trans f) (OrbitMinimum.Construction.abs_det_one_trans e f he hf)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.EuclideanRepresentation.Construction
