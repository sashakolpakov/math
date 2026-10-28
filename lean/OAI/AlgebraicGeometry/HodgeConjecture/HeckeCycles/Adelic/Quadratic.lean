import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.BareGenerators
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CoverFields
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuadraticProjection

/-! # Quadratic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Quadratic.CM

noncomputable section

/-! Actual adelic upper lifts and their exact quadratic multiplier
formula, derived from the real and finite bare generators. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ConstructedAdelicGroup.CM
variable (n : ℕ)

def upper (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm) : Constructed.ConstructedAdelicGroup.CM.AdelicGroup n :=
  AdelicPairGroup.CM.assemble (Constructed.RealCover.CM.realCover n)
    (Finite.ConstructedCover.CM.finiteCover (Fin n))
    (Real.BareGenerators.CM.upper n ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩,
      Finite.QuadraticBare.CM.quadraticLift (B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hB.map _))

theorem upper_projection_matrix (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm) :
    (Constructed.ConstructedAdelicGroup.CM.projection n (upper n B hB)).val = Matrix.fromBlocks 1 B 0 1 := by
  change (AdelicPairGroup.CM.projection _ _ (AdelicPairGroup.CM.assemble _ _ _)).val = _
  rw [AdelicPairGroup.CM.projection_assemble]
  change SymplecticProduct.CM.pairMatrix
    (Real.SchrodingerAction.CM.projection n (Real.BareGenerators.CM.upper n
      ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩)).val
    (((Finite.ConstructedCover.CM.finiteCover (Fin n)).project
      (Finite.QuadraticBare.CM.quadraticLift (B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (hB.map _))).val) = _
  rw [Real.BareGenerators.CM.upper_projection, Finite.CoverFields.CM.projection_matrix,
    Finite.QuadraticBare.CM.quadraticLift_projection]
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases hij : i = j <;> simp [SymplecticProduct.CM.pairMatrix, RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper, hij]
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j =>
      by_cases hij : i = j <;> simp [SymplecticProduct.CM.pairMatrix, RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringUpper, hij]

theorem upper_tensor (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    Constructed.ConstructedAdelicGroup.CM.action n (upper n B hB) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor
      (Real.SchrodingerAction.CM.action n (Real.BareGenerators.CM.upper n
        ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩) f)
      (Finite.Quadratic.CM.finiteQuadratic (B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) φ) := by
  change AdelicPairGroup.CM.action _ _ (AdelicPairGroup.CM.assemble _ _ _) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = _
  rw [AdelicPairGroup.CM.action_assemble, ProductOperators.CM.operator_tensor,
    Finite.CoverFields.CM.action, Finite.QuadraticBare.CM.quadraticLift_action]
  rfl

def raw (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) →ₗ[ℂ] ((Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) where
  toFun F x := Constructed.AdelicCharacter.CM.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) * F.val x
  map_add' F G := by funext x; exact mul_add _ _ _
  map_smul' c F := by funext x; exact mul_left_comm _ _ _

theorem phase_split (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    Constructed.AdelicCharacter.CM.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (fun i => (x i).1)) *
      Constructed.AdelicCharacter.CM.Finite.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) (fun i => (x i).2)) := by
  rw [Constructed.AdelicCharacter.CM.character_apply]
  have hr := QuadraticProjection.CM.quadratic_map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf).toRatAlgHom B x
  have hf := QuadraticProjection.CM.quadratic_map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf).toRatAlgHom B x
  change (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x).1 = _ at hr
  change (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x).2 = _ at hf
  rw [hr, hf]
  rfl

theorem upper_raw (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)).subtype.comp (Constructed.ConstructedAdelicGroup.CM.action n (upper n B hB)).toLinearMap = raw n B := by
  apply FiniteOperators.CM.Sections.linear_ext
  intro f φ
  change (Constructed.ConstructedAdelicGroup.CM.action n (upper n B hB) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ)).val = _
  rw [upper_tensor]
  funext x
  change (Real.SchrodingerAction.CM.action n (Real.BareGenerators.CM.upper n
      ⟨B.map (RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf), hB.map _⟩) f).val (fun i => (x i).1) *
    (Finite.Quadratic.CM.finiteQuadratic (B.map (RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) φ).val (fun i => (x i).2) = _
  rw [Real.BareGenerators.CM.upper_apply, Finite.Quadratic.CM.finiteQuadratic_apply]
  change (_ * f.val (fun i => (x i).1)) * (_ * φ.val (fun i => (x i).2)) =
    Constructed.AdelicCharacter.CM.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) *
      (f.val (fun i => (x i).1) * φ.val (fun i => (x i).2))
  rw [phase_split]
  ring

theorem upper_apply (B : Matrix (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) (hB : B.IsSymm)
    (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (Constructed.ConstructedAdelicGroup.CM.action n (upper n B hB) F).val x = Constructed.AdelicCharacter.CM.character (RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic B x) * F.val x :=
  congrFun (LinearMap.congr_fun (upper_raw n B hB) F) x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Quadratic.CM
