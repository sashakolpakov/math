import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairSupportedCupIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairCompactSupport

/-! # Normal Pair Compact Gysin -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairCompactGysin.Constructions

noncomputable section

/-!
# DegreeTwo: compact-support Gysin map in an actual normal pair

The map uses the actual exterior cup and actual homeomorphism pullback.
At every compact tangential support it is cup with the specified normal
pair class, inserted at the genuine compact subset of the immersion image.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {c : ℕ} {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)

def normalPairCompactGysin (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) q →ₗ[ℚ]
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) (2*c+q) :=
  (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of P.neighborhood)
    (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))
    (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) (2*c+q)).hom.hom.comp
    (CompactExteriorCup.Constructions.compactExteriorCup (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P)) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (2*c) q
      (NestedOpenPointClass.Constructions.compactOpenPointDualClass (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)))

theorem normalPairCompactGysin_stage (K : Compacts (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ q) :
    normalPairCompactGysin P q
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) K q a) =
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of P.neighborhood)
      (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) (2*c+q)).hom
      (CompactExteriorCup.Constructions.compactExteriorCupStage (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P)) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
        ⟨{NormalPairProductSupport.Constructions.normalPairNormalOrigin P},isCompact_singleton⟩ K (2*c) q
        (NestedOpenPointClass.Constructions.openOriginRelativeDualClass (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)) a) := by
  let _ := (inferInstance : NormedSpace ℝ E)
  exact congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of P.neighborhood)
    (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))
    (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) (2*c+q)).hom
    (CompactExteriorCup.Constructions.compactExteriorCup_stage (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P)) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      ⟨{NormalPairProductSupport.Constructions.normalPairNormalOrigin P},isCompact_singleton⟩ K (2*c) q
      (NestedOpenPointClass.Constructions.openOriginRelativeDualClass (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)) a)

theorem normalPairCompactGysin_stage_supported (K : Compacts (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ q) :
    normalPairCompactGysin P q
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) K q a) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) (NormalPairCompactSupport.Constructions.normalPairCompactSupport P K) (2*c+q)
      (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of P.neighborhood) S (2*c+q)) (NormalPairCompactSupport.Constructions.normalPairCompactSupport_complement P K))
        (PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso P (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ
          K.isCompact.isClosed.isOpen_compl q a)) := by
  rw [normalPairCompactGysin_stage]
  have h := NormalPairCompactSupport.Constructions.normalPairCompactSupport_cohomology P K (2*c+q)
    (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P)) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      ({NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ) (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ
      isClosed_singleton.isOpen_compl K.isCompact.isClosed.isOpen_compl (2*c) q
      (NestedOpenPointClass.Constructions.openOriginRelativeDualClass (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)) a)
  have he : PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso P (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ
      K.isCompact.isClosed.isOpen_compl q a =
      (NormalPairProductSupport.Constructions.normalPairProductCohomologyIso P (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ (2*c+q)).hom
        (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P)) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
          ({NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ) (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ
          isClosed_singleton.isOpen_compl K.isCompact.isClosed.isOpen_compl (2*c) q
          (NestedOpenPointClass.Constructions.openOriginRelativeDualClass (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)) a) := by
    unfold PairSupportedCupIso.Constructions.normalPairSupportedCohomologyIso
    rw [LinearEquiv.trans_apply, OpenNormal.Constructions.openNormalSupportedCohomologyIso_eq_cup]
    rfl
  exact h.trans (congrArg
    (fun z => AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (NormalPairCompactSupport.Constructions.normalPairCompactSupport P K) (2*c+q)
      (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of P.neighborhood) S (2*c+q)) (NormalPairCompactSupport.Constructions.normalPairCompactSupport_complement P K)) z)) he.symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairCompactGysin.Constructions
