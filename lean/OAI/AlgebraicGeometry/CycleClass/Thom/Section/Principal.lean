import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CycleLift
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal

/-! # Principal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.Principal.Constructions.Class

noncomputable section

/-! The actual section principal cycle has one globally supported class.
Its classes on analytic opens are restrictions of that class, and agree
with the canonical finite-cycle classes used by the local cup formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CycleLift.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)

local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.sectionClosedSupport D B s
local notation "q" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.dimensionCodimension V D.val + 1
local notation "c" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions.normalizedPrincipalCycle V D.val (OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs
local notation "T" => TopCat.of V.analyticSpace
local notation "O" => (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ

 theorem principalCycle_supported (C : Geometric.DimensionCycles.DimensionCycleSupport V q) (hC : c C ≠ 0) :
    (C.val : Set V.carrier) ⊆ F := by
  apply ClosedSupport.Constructions.principalCoefficient_subset_sectionClosedSupport D B s C.val
  rwa [Normalization.Principal.Constructions.normalizedPrincipalCycle_coefficient] at hC

 def sectionSupportedCycle : Supported.Map.Constructions.SupportedCycle V F q := Supported.CycleLift.Constructions.liftCycle V F q c

 theorem sectionSupportedCycle_forget :
    Supported.Map.Constructions.forgetCycle V F q (sectionSupportedCycle D B s hs) = c :=
  Supported.CycleLift.Constructions.forget_liftCycle V F q c (principalCycle_supported D B s hs)

 def sectionPrincipalClass (U : Opens V.analyticSpace) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O U) (2 * q) :=
  Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T O U (2 * q)
    (Supported.Map.Constructions.relativeClassMap V F q (sectionSupportedCycle D B s hs))

 theorem sectionPrincipalClass_eq_local (U : Opens V.analyticSpace) :
    sectionPrincipalClass D B s hs U =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U {x : U | V.analyticUnderlying x.val ∈ F} q
      (Open.SupportedLift.Constructions.restrictCycle V U {x : U | V.analyticUnderlying x.val ∈ F} q c) :=
  (Supported.CycleLift.Constructions.supportedClass_on_open V F q c (principalCycle_supported D B s hs) U).symm

 theorem sectionPrincipalClass_restrict (U P : Opens V.analyticSpace) (hPU : P ≤ U) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) T O (2 * q)).map (homOfLE hPU).op
      (sectionPrincipalClass D B s hs U) = sectionPrincipalClass D B s hs P := by
  exact ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    ((Opens.toTopCat T).map (homOfLE hPU)) (Geometric.LocalHomology.Cycles.subspaceInclusion T (U : Set V.analyticSpace))
    (A := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O P) (B := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O U) (C := O)
    (fun _ hx => hx) (fun _ hx => hx) (2 * q))
    (Supported.Map.Constructions.relativeClassMap V F q (sectionSupportedCycle D B s hs))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.Principal.Constructions.Class
