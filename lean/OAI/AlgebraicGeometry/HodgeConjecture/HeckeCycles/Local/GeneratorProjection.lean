import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.GeneratorFamily
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticCoordinateLemmas

/-! # Generator Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.GeneratorProjection.CM

noncomputable section

/-! The local lifts used in the finite-product construction have the
actual prime projections of the global upper and lower generators. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OperatorFamily.CM.LocalFamily
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.GeneratorFamily.CM.Family
variable (n : ℕ)
local instance (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : MeasurableSpace ℚ_[OperatorFamily.CM.LocalFamily.number v] := borel ℚ_[OperatorFamily.CM.LocalFamily.number v]
local instance (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : BorelSpace ℚ_[OperatorFamily.CM.LocalFamily.number v] := ⟨rfl⟩

theorem global_matrix (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (g : Finite.FiniteOscillator.CM.Oscillator (I := Fin n)) :
    (OperatorFamily.CM.LocalFamily.globalProjection n v g).val = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap *
      (Finite.FiniteOscillator.CM.projection g).val.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v)) * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap := by
  unfold OperatorFamily.CM.LocalFamily.globalProjection
  simp only [MonoidHom.comp_apply]
  exact SymplecticCoordinateLemmas.CM.reindex_map_swap_matrix
    (Classical.decEq _) inferInstance (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v)).toRingHom
      (Finite.FiniteOscillator.CM.projection g)

theorem upper_projection (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    OperatorFamily.CM.LocalFamily.localProjection n v (GeneratorFamily.CM.Family.upper n B hB v) =
      OperatorFamily.CM.LocalFamily.globalProjection n v (Finite.Quadratic.CM.quadraticOscillator B hB) := by
  have h := RepresentationTheory.Weil.Local.NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic_projection
    (RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice.Realization.padic_not_discrete (OperatorFamily.CM.LocalFamily.number v)) (PadicCharacter.CM.character (OperatorFamily.CM.LocalFamily.number v))
    (PadicCharacter.CM.character_unitary (OperatorFamily.CM.LocalFamily.number v))
    (PadicCharacter.CM.character_continuous (OperatorFamily.CM.LocalFamily.number v))
    (⟨B.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v)), hB.map _⟩ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ_[OperatorFamily.CM.LocalFamily.number v] n)
  change OperatorFamily.CM.LocalFamily.localProjection n v (GeneratorFamily.CM.Family.upper n B hB v) = _ at h
  rw [h]
  apply Subtype.ext
  rw [global_matrix]
  have hg : Finite.FiniteOscillator.CM.projection (Finite.Quadratic.CM.quadraticOscillator B hB) =
      @RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf _ _ (Classical.decEq _) B hB :=
    Finite.QuadraticBare.CM.quadraticLift_projection B hB
  rw [hg]
  change Matrix.fromBlocks 1 0 (B.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v))) 1 =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * ((@RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf _ _ (Classical.decEq _) B hB).val.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v))) * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap
  simp [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper, Matrix.fromBlocks_map, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap_conjugation]
  all_goals
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem lower_projection (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    OperatorFamily.CM.LocalFamily.localProjection n v (GeneratorFamily.CM.Family.lower n B hB v) =
      OperatorFamily.CM.LocalFamily.globalProjection n v (Finite.IntegralVacuum.CM.LowerBare.lowerLift B hB).val := by
  have h := PrimeQuadratic.CM.Lower.conjugateQuadratic_projection (OperatorFamily.CM.LocalFamily.number v) n
    ⟨B.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v)), hB.map _⟩
  change OperatorFamily.CM.LocalFamily.localProjection n v (GeneratorFamily.CM.Family.lower n B hB v) = _ at h
  rw [h]
  apply Subtype.ext
  rw [global_matrix]
  have hg : Finite.FiniteOscillator.CM.projection (Finite.IntegralVacuum.CM.LowerBare.lowerLift B hB).val =
      Finite.IntegralVacuum.CM.LowerBare.lower B hB := Finite.IntegralVacuum.CM.LowerBare.lowerLift_projection B hB
  rw [hg]
  change Matrix.fromBlocks 1 (B.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v))) 0 1 =
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap * ((Finite.IntegralVacuum.CM.LowerBare.lower B hB).val.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v))) * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap
  simp [Finite.IntegralVacuum.CM.LowerBare.lower, Matrix.fromBlocks_map, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.coordinateSwap_conjugation]
  all_goals
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem upper_realized (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    Finite.Quadratic.CM.quadraticOscillator B hB ∈ OperatorFamily.CM.LocalFamily.realized n :=
  ⟨GeneratorFamily.CM.Family.upper n B hB, upper_projection n B hB, GeneratorFamily.CM.Family.upper_eventual n B hB⟩

theorem lower_realized (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) :
    (Finite.IntegralVacuum.CM.LowerBare.lowerLift B hB).val ∈ OperatorFamily.CM.LocalFamily.realized n :=
  ⟨GeneratorFamily.CM.Family.lower n B hB, lower_projection n B hB, GeneratorFamily.CM.Family.lower_eventual n B hB⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.GeneratorProjection.CM
