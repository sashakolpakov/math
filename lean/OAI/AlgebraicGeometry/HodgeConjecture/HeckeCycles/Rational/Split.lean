import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Lower
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.ThetaGraph
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Poisson
import OAI.RepresentationTheory.Weil.Local.GenerationSymplectic

/-! # Split -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Split.CM.Unipotents

/-! Rational upper and lower generators have actual theta-preserving
lifts in the constructed adelic group. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Weil.Local.GenerationSymplectic.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM
variable (n : ℕ)

theorem rational_phase (B : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    Constructed.AdelicCharacter.CM.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (B.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)) = 1 := by
  have h := QuadraticProjection.CM.quadratic_map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ).toRatAlgHom B x
  change algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) = RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (B.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x) at h
  rw [← h]
  exact Constructed.AdelicCharacter.CM.character_rational _

theorem upper_theta (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm)
    (hphase : ∀ x : Fin n → ℚ, Constructed.AdelicCharacter.CM.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)) = 1)
    (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) :
    RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Constructed.ConstructedAdelicGroup.CM.action n (Adelic.Quadratic.CM.upper n B hB) F) = RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional F := by
  apply tsum_congr
  intro x
  rw [Adelic.Quadratic.CM.upper_apply, hphase, one_mul]

theorem lower_theta (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm)
    (hphase : ∀ x : Fin n → ℚ, Constructed.AdelicCharacter.CM.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)) = 1)
    (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) :
    RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Constructed.ConstructedAdelicGroup.CM.action n (Adelic.Lower.CM.lower n B hB) F) = RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional F := by
  have hneg : ∀ x : Fin n → ℚ,
      Constructed.AdelicCharacter.CM.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (-B) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)) = 1 := by
    intro x
    rw [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic_neg, AddChar.map_neg_eq_inv, hphase, inv_one]
  rw [Adelic.Lower.CM.lower_action]
  change RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional ((Adelic.Fourier.CM.fourierEquiv n).symm
    (Constructed.ConstructedAdelicGroup.CM.action n (Adelic.Quadratic.CM.upper n (-B) hB.neg) (Adelic.Fourier.CM.fourierEquiv n F))) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional F
  rw [Constructed.Poisson.CM.theta_inverse_fourier]
  change RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional
    (Constructed.ConstructedAdelicGroup.CM.action n (Adelic.Quadratic.CM.upper n (-B) hB.neg) (Adelic.Fourier.CM.fourierEquiv n F)) = RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional F
  rw [upper_theta n (-B) hB.neg hneg]
  exact Constructed.Poisson.CM.theta_fourier_invariant n F

def upper (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ n) : Constructed.ConstructedAdelicGroup.CM.AdelicGroup n :=
  Adelic.Quadratic.CM.upper n (B.val.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) (B.property.map _)

def lower (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ n) : Constructed.ConstructedAdelicGroup.CM.AdelicGroup n :=
  Adelic.Lower.CM.lower n (B.val.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) (B.property.map _)

theorem upper_covers (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ n) :
    Constructed.ConstructedAdelicGroup.CM.projection n (upper n B) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (RepresentationTheory.Weil.Local.GenerationSymplectic.Construction.upperSymplectic B) := by
  apply Subtype.ext
  rw [upper, Adelic.Quadratic.CM.upper_projection_matrix]
  change Matrix.fromBlocks 1 (B.val.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) 0 1 =
    (Matrix.fromBlocks 1 B.val 0 1).map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)
  simp [Matrix.fromBlocks_map]

theorem lower_covers (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ n) :
    Constructed.ConstructedAdelicGroup.CM.projection n (lower n B) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (RepresentationTheory.Weil.Local.Generators.Construction.quadraticSymplectic B) := by
  apply Subtype.ext
  rw [lower, Adelic.Lower.CM.lower_projection_matrix]
  change Matrix.fromBlocks 1 0 (B.val.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) 1 =
    (Matrix.fromBlocks 1 0 B.val 1).map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)
  simp [Matrix.fromBlocks_map]

theorem upper_graph (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ n) :
    (RepresentationTheory.Weil.Local.GenerationSymplectic.Construction.upperSymplectic B, upper n B) ∈ ThetaGraph.CM.graph n :=
  ⟨upper_covers n B, upper_theta n (B.val.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) (B.property.map _) (rational_phase n B.val)⟩

theorem lower_graph (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ n) :
    (RepresentationTheory.Weil.Local.Generators.Construction.quadraticSymplectic B, lower n B) ∈ ThetaGraph.CM.graph n :=
  ⟨lower_covers n B, lower_theta n (B.val.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) (B.property.map _) (rational_phase n B.val)⟩

theorem rationalProjection_surjective : Function.Surjective (ThetaGraph.CM.rationalProjection n) := by
  apply MonoidHom.range_eq_top.mp
  apply RepresentationTheory.Weil.Local.GenerationSymplectic.Construction.subgroup_eq_top_of_symplectic_unipotents
  · intro B
    exact MonoidHom.mem_range.mpr ⟨⟨(RepresentationTheory.Weil.Local.GenerationSymplectic.Construction.upperSymplectic B, upper n B), upper_graph n B⟩, rfl⟩
  · intro B
    exact MonoidHom.mem_range.mpr ⟨⟨(RepresentationTheory.Weil.Local.Generators.Construction.quadraticSymplectic B, lower n B), lower_graph n B⟩, rfl⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Split.CM.Unipotents

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Split.CM

/-! The rational splitting is constructed as the unique actual
adelic lift preserving the nonzero theta functional. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Weil.Local.GenerationSymplectic.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM
variable (n : ℕ)

def graphEquiv : ThetaGraph.CM.graph n ≃* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ :=
  MulEquiv.ofBijective (ThetaGraph.CM.rationalProjection n)
    ⟨ThetaGraph.CM.rationalProjection_injective n,
      Unipotents.rationalProjection_surjective n⟩

def split : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ →* Constructed.ConstructedAdelicGroup.CM.AdelicGroup n :=
  (MonoidHom.snd _ _).comp ((ThetaGraph.CM.graph n).subtype.comp (graphEquiv n).symm.toMonoidHom)

theorem lift_first (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ) : ((graphEquiv n).symm γ).val.1 = γ :=
  (graphEquiv n).apply_symm_apply γ

theorem split_graph (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ) : (γ, split n γ) ∈ ThetaGraph.CM.graph n := by
  have h := ((graphEquiv n).symm γ).property
  have he : ((graphEquiv n).symm γ).val = (γ, split n γ) :=
    Prod.ext (lift_first n γ) rfl
  rwa [he] at h

theorem graph_iff (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ) (a : Constructed.ConstructedAdelicGroup.CM.AdelicGroup n) :
    (γ, a) ∈ ThetaGraph.CM.graph n ↔ split n γ = a := by
  constructor
  · intro ha
    have he : (graphEquiv n).symm γ = ⟨(γ, a), ha⟩ := by
      apply ThetaGraph.CM.rationalProjection_injective n
      exact lift_first n γ
    exact congrArg (fun b : ThetaGraph.CM.graph n => b.val.2) he
  · rintro rfl
    exact split_graph n γ

theorem split_covers (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ) : Constructed.ConstructedAdelicGroup.CM.projection n (split n γ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) γ :=
  (split_graph n γ).1

theorem theta_invariant (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ) (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) :
    RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional (Constructed.ConstructedAdelicGroup.CM.action n (split n γ) F) = RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional F :=
  (split_graph n γ).2 F

theorem split_upper (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ n) :
    split n (RepresentationTheory.Weil.Local.GenerationSymplectic.Construction.upperSymplectic B) = Unipotents.upper n B :=
  (graph_iff n _ _).mp (Unipotents.upper_graph n B)

theorem split_lower (B : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.SymmetricMatrix ℚ n) :
    split n (RepresentationTheory.Weil.Local.Generators.Construction.quadraticSymplectic B) = Unipotents.lower n B :=
  (graph_iff n _ _).mp (Unipotents.lower_graph n B)

theorem rational_quadratic (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : B.IsSymm) (hγ : γ.val = Matrix.fromBlocks 1 B 0 1)
    (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (Constructed.ConstructedAdelicGroup.CM.action n (split n γ) F).val x =
      Constructed.AdelicCharacter.CM.character (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ (1 / 2) *
        (x ⬝ᵥ (B.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x))) * F.val x := by
  have he : γ = RepresentationTheory.Weil.Local.GenerationSymplectic.Construction.upperSymplectic ⟨B, hB⟩ := Subtype.ext hγ
  rw [he, split_upper]
  exact Adelic.Quadratic.CM.upper_apply n _ _ F x

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Split.CM

end

end OAI
