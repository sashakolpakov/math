import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairProductSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalResidueChartNaturality

/-! # Pair Supported Cup Iso -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairSupportedCupIso.Constructions

noncomputable section

/-!
# DegreeTwo: the Thom isomorphism in actual immersion neighborhoods

The map is the genuine supported cup with the normal pair's specified
relative class and the actual tangential pullback, in every degree.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {c : ℕ} {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)

theorem normalPairFirstMap_normal_mapsTo :
    Set.MapsTo (NormalPairProductSupport.Constructions.normalPairFirstMap P) P.relativeComplement
      (Prod.fst ⁻¹' ({NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ : Set (NormalPairProductSupport.Constructions.normalPairNormalOpen P))) :=
  fun y hy => (NormalPairProductSupport.Constructions.normalPairFirstMap_complement P y).mp hy

theorem normalPairFirstMap_tangent_mapsTo (B : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) :
    Set.MapsTo (NormalPairProductSupport.Constructions.normalPairFirstMap P) (NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B) (Prod.snd ⁻¹' B) := by
  let _ := (inferInstance : NormedSpace ℝ E)
  exact fun _ hx => hx

theorem normalPairFirstNormal_pullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairFirstMap P)
      (normalPairFirstMap_normal_mapsTo P) (2*c)
      (NormalResidueChartNaturality.Constructions.firstNormalOpenClass (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)
        (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))) = P.rationalClassFin := by
  unfold NormalResidueChartNaturality.Constructions.firstNormalOpenClass NestedOpenPointClass.Constructions.openOriginRelativeDualClass
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin c → ℂ)) (NormalPairProductSupport.Constructions.normalPairNormalOpen P))
      (NestedOpenPointClass.Constructions.openOrigin_mapsTo_complement (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)) (2*c) ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (ProductSupportRetraction.Constructions.tangentProjection (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (A := Prod.fst ⁻¹' ({NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ : Set (NormalPairProductSupport.Constructions.normalPairNormalOpen P)))
      (B := ({NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ : Set (NormalPairProductSupport.Constructions.normalPairNormalOpen P))) (fun _ hx => hx) (2*c) ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairFirstMap P)
      (normalPairFirstMap_normal_mapsTo P) (2*c)) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c) = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp,
    P.rationalClassFin_eq_normalPullback]
  rfl

theorem normalPairTangent_pullback (B : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairFirstMap P)
      (normalPairFirstMap_tangent_mapsTo P B) q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
        (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx) q a) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P)
      (A := NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B) (B := B) (fun _ hx => hx) q a := by
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx) q ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairFirstMap P)
      (normalPairFirstMap_tangent_mapsTo P B) q) a = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

def normalPairSupportedCohomologyIso (B : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (hB : IsOpen B) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) B q ≃ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (NormalPairProductSupport.Constructions.normalPairCombinedComplement P B) (2*c+q) :=
  (OpenNormal.Constructions.openNormalSupportedCohomologyIso (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)
    (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) B hB q).trans
    (NormalPairProductSupport.Constructions.normalPairProductCohomologyIso P B (2*c+q)).toLinearEquiv

theorem normalPairSupportedCohomologyIso_eq_cup (B : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (hB : IsOpen B)
    (q : ℕ) (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) B q) :
    normalPairSupportedCohomologyIso P B hB q a =
    SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of P.neighborhood) P.relativeComplement (NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B)
      (NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (hB.preimage (NormalPairProductSupport.Constructions.normalPairTangentMap P).hom.continuous)
      (2*c) q P.rationalClassFin
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPairProductSupport.Constructions.normalPairTangentMap P)
        (A := NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B) (B := B) (fun _ hx => hx) q a) := by
  have hN : IsOpen ({NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ : Set (NormalPairProductSupport.Constructions.normalPairNormalOpen P)) :=
    isClosed_singleton.isOpen_compl
  have hc := SupportCup.Constructions.twoSupportCohomologyCup_naturality (TopCat.of P.neighborhood)
    P.relativeComplement (NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B)
    (NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (hB.preimage (NormalPairProductSupport.Constructions.normalPairTangentMap P).hom.continuous)
    (2*c) q (NormalPairProductSupport.Constructions.normalPairFirstMap P)
    (Prod.fst ⁻¹' ({NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ : Set (NormalPairProductSupport.Constructions.normalPairNormalOpen P))) (Prod.snd ⁻¹' B)
    (hN.preimage continuous_fst) (hB.preimage continuous_snd)
    (normalPairFirstMap_normal_mapsTo P) (normalPairFirstMap_tangent_mapsTo P B)
    (NormalResidueChartNaturality.Constructions.firstNormalOpenClass (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)))
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.NormalProductPair.Cycles.normalProductProjection (NormalPairProductSupport.Constructions.normalPairNormalOpen P) (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx) q a)
  have hl := congrArg₂
    (fun u v => SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of P.neighborhood) P.relativeComplement
      (NormalPairProductSupport.Constructions.normalPairTangentMap P ⁻¹' B) (NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P)
      (hB.preimage (NormalPairProductSupport.Constructions.normalPairTangentMap P).hom.continuous) (2*c) q u v)
    (normalPairFirstNormal_pullback P) (normalPairTangent_pullback P B q a)
  unfold normalPairSupportedCohomologyIso
  rw [LinearEquiv.trans_apply, OpenNormal.Constructions.openNormalSupportedCohomologyIso_eq_cup]
  change (NormalPairProductSupport.Constructions.normalPairProductCohomologyIso P B (2*c+q)).hom _ = _
  rw [NormalPairProductSupport.Constructions.normalPairProductCohomologyIso_hom]
  exact hc.symm.trans hl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PairSupportedCupIso.Constructions
