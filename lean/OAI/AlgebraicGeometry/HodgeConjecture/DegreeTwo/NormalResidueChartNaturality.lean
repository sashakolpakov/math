import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenNormal
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChartCupNaturality

/-! # Normal Residue Chart Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalResidueChartNaturality.Constructions

noncomputable section

/-!
# DegreeTwo: inverse local Thom maps commute with changes of normal coordinates

The hypotheses retain the literal support maps, zero-section equality,
normal contraction, and equality of the actual pulled-back normal classes.
The conclusion concerns all degrees and all supported classes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

def firstNormalOpenClass {c : ℕ} (U : Opens (Fin c → ℂ)) (h0 : (0 : Fin c → ℂ) ∈ U)
    (Y : TopCat.{0}) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U×Y))
      (Prod.fst ⁻¹' ({⟨0,h0⟩}ᶜ : Set U)) (2*c) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (ProductSupportRetraction.Constructions.tangentProjection U Y)
    (A := Prod.fst ⁻¹' ({⟨0,h0⟩}ᶜ : Set U)) (B := ({⟨0,h0⟩}ᶜ : Set U))
    (fun _ hx => hx) (2*c) (NestedOpenPointClass.Constructions.openOriginRelativeDualClass U h0)

variable {c : ℕ} (U U' : Opens (Fin c → ℂ))
variable (h0 : (0 : Fin c → ℂ) ∈ U) (h0' : (0 : Fin c → ℂ) ∈ U')
variable {Y Y' : TopCat.{0}} (f : TopCat.of (U×Y) ⟶ TopCat.of (U'×Y')) (g : Y ⟶ Y')
variable (H : ContinuousMap.Homotopy (ContinuousMap.const U ⟨0,h0⟩) (ContinuousMap.id U))
variable (hsec : CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection U Y ⟨0,h0⟩ ≫ f = g ≫ CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection U' Y' ⟨0,h0'⟩)
variable (B : Set Y) (B' : Set Y') (hB : IsOpen B) (hB' : IsOpen B')
variable (hfA : Set.MapsTo f (Prod.fst ⁻¹' ({⟨0,h0⟩}ᶜ : Set U))
  (Prod.fst ⁻¹' ({⟨0,h0'⟩}ᶜ : Set U')))
variable (hfB : Set.MapsTo f (Prod.snd ⁻¹' B) (Prod.snd ⁻¹' B')) (hg : Set.MapsTo g B B')
variable (hnormal : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
  (A := Prod.fst ⁻¹' ({⟨0,h0⟩}ᶜ : Set U)) (B := Prod.fst ⁻¹' ({⟨0,h0'⟩}ᶜ : Set U')) hfA (2*c)
  (firstNormalOpenClass U' h0' Y') = firstNormalOpenClass U h0 Y)

include H hsec hnormal in
theorem openNormalSupportedCohomologyIso_chart_naturality (q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y' B' q) :
    OpenNormal.Constructions.openNormalSupportedCohomologyIso U h0 Y B hB q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q a) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f (hfA.union_union hfB) (2*c+q)
      (OpenNormal.Constructions.openNormalSupportedCohomologyIso U' h0' Y' B' hB' q a) := by
  rw [OpenNormal.Constructions.openNormalSupportedCohomologyIso_eq_cup, OpenNormal.Constructions.openNormalSupportedCohomologyIso_eq_cup]
  exact ChartCupNaturality.Constructions.relativeExteriorCup_chart_naturality (X := TopCat.of U) (X' := TopCat.of U')
    (Y := Y) (Y' := Y') f g (⟨0,h0⟩ : U) (⟨0,h0'⟩ : U') H hsec
    ({⟨0,h0⟩}ᶜ : Set U) ({⟨0,h0'⟩}ᶜ : Set U') B B'
    isClosed_singleton.isOpen_compl isClosed_singleton.isOpen_compl hB hB'
    hfA hfB hg (2*c) q (NestedOpenPointClass.Constructions.openOriginRelativeDualClass U h0) (NestedOpenPointClass.Constructions.openOriginRelativeDualClass U' h0') hnormal a

include H hsec hnormal in
theorem openNormalResidue_chart_naturality (q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U'×Y'))
      (RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of U') Y' ({⟨0,h0'⟩}ᶜ) B') (2*c+q)) :
    (OpenNormal.Constructions.openNormalSupportedCohomologyIso U h0 Y B hB q).symm
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f (hfA.union_union hfB) (2*c+q) b) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q
      ((OpenNormal.Constructions.openNormalSupportedCohomologyIso U' h0' Y' B' hB' q).symm b) := by
  let es := OpenNormal.Constructions.openNormalSupportedCohomologyIso U h0 Y B hB q
  let et := OpenNormal.Constructions.openNormalSupportedCohomologyIso U' h0' Y' B' hB' q
  have h := openNormalSupportedCohomologyIso_chart_naturality U U' h0 h0' f g H hsec B B' hB hB'
    hfA hfB hg hnormal q (et.symm b)
  have h' : es (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q (et.symm b)) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f (hfA.union_union hfB) (2*c+q) b :=
    h.trans (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
      (hfA.union_union hfB) (2*c+q)) (et.apply_symm_apply b))
  exact (congrArg es.symm h').symm.trans (es.symm_apply_apply _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalResidueChartNaturality.Constructions
