import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairProductSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactRelativeExteriorCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactPointNaturality

/-! # Normal Pair Compact Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairCompactSupport.Constructions

noncomputable section

/-! Actual compact supports over compact tangential subsets of a normal pair. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {c : ℕ} {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)

def normalPairProductCompact (K : Compacts (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) :
    Compacts (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P) :=
  ⟨{NormalPairProductSupport.Constructions.normalPairNormalOrigin P},isCompact_singleton⟩ ×ˢ K

def normalPairCompactSupport (K : Compacts (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) : Compacts P.neighborhood :=
  Compacts.equiv (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P).symm (normalPairProductCompact P K)

theorem normalPairCompactSupport_image (K : Compacts (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) :
    Compacts.equiv (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) (normalPairCompactSupport P K) = normalPairProductCompact P K := by
  let _ := (inferInstance : NormedSpace ℝ E)
  rw [normalPairCompactSupport, Compacts.equiv_symm, Equiv.apply_symm_apply]

theorem normalPairCompactSupport_complement (K : Compacts (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) :
    NormalPairProductSupport.Constructions.normalPairCombinedComplement P (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ =
      (normalPairCompactSupport P K : Set P.neighborhood)ᶜ := by
  have he : NormalPairProductSupport.Constructions.normalPairCombinedComplement P (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ =
      NormalPairProductSupport.Constructions.normalPairFirstMap P ⁻¹'
        RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P)) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
          ({NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ) (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ :=
    Set.ext (NormalPairProductSupport.Constructions.normalPairFirstMap_combinedComplement P (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ)
  have hc := congrArg
    (fun S : Set (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P) => NormalPairProductSupport.Constructions.normalPairFirstMap P ⁻¹' S)
    (CompactExteriorCup.Constructions.compactProductComplement (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P))
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) ⟨{NormalPairProductSupport.Constructions.normalPairNormalOrigin P},isCompact_singleton⟩ K)
  have hk : NormalPairProductSupport.Constructions.normalPairFirstMap P ⁻¹'
      (normalPairProductCompact P K : Set (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ =
      (normalPairCompactSupport P K : Set P.neighborhood)ᶜ := by
    rw [normalPairCompactSupport, Compacts.coe_equiv_apply_eq_preimage, Homeomorph.symm_symm]
    rfl
  exact he.trans (hc.trans hk)

theorem normalPairCompactSupport_mapsTo (K : Compacts (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) :
    Set.MapsTo (NormalPairProductSupport.Constructions.normalPairFirstMap P) (normalPairCompactSupport P K : Set P.neighborhood)ᶜ
      (normalPairProductCompact P K : Set (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ := by
  let _ := (inferInstance : NormedSpace ℝ E)
  intro y hy
  rw [normalPairCompactSupport, Compacts.coe_equiv_apply_eq_preimage, Homeomorph.symm_symm] at hy
  exact hy

theorem normalPairCompactSupport_cohomology (K : Compacts (NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P)) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
        ({NormalPairProductSupport.Constructions.normalPairNormalOrigin P}ᶜ) (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ) n) :
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of P.neighborhood)
      (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) n).hom
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
        (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (normalPairProductCompact P K) n
        (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
          (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P)) S n)
          (CompactExteriorCup.Constructions.compactProductComplement (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P)) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
            ⟨{NormalPairProductSupport.Constructions.normalPairNormalOrigin P},isCompact_singleton⟩ K)) a)) =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) (normalPairCompactSupport P K) n
      (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) S n)
        (normalPairCompactSupport_complement P K))
        ((NormalPairProductSupport.Constructions.normalPairProductCohomologyIso P (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ n).hom a)) := by
  have hi := CompactPointNaturality.Constructions.compactSupportHomeomorphStage_map (X := TopCat.of P.neighborhood)
    (Y := TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))
    (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P) (normalPairCompactSupport P K) (normalPairProductCompact P K)
    (congrArg (fun C : Compacts (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P) =>
      (C : Set (NormalPairProductSupport.Constructions.normalPairNormalOpen P × NormalPairProductSupport.Constructions.normalPairTangentSpace P))) (normalPairCompactSupport_image P K))
    (normalPairCompactSupport_mapsTo P K) n
  have hc := CompactRelativeExteriorCup.Constructions.relativePairCohomology_supportCast (NormalPairProductSupport.Constructions.normalPairFirstMap P)
    (normalPairCompactSupport_complement P K)
    (CompactExteriorCup.Constructions.compactProductComplement (TopCat.of (NormalPairProductSupport.Constructions.normalPairNormalOpen P)) (TopCat.of (NormalPairProductSupport.Constructions.normalPairTangentSpace P))
      ⟨{NormalPairProductSupport.Constructions.normalPairNormalOrigin P},isCompact_singleton⟩ K)
    (fun y hy => (NormalPairProductSupport.Constructions.normalPairFirstMap_combinedComplement P (K : Set (NormalPairProductSupport.Constructions.normalPairTangentSpace P))ᶜ y).mp hy)
    (normalPairCompactSupport_mapsTo P K) n a
  exact (ConcreteCategory.congr_hom hi _).symm.trans
    (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (normalPairCompactSupport P K) n) hc)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairCompactSupport.Constructions
