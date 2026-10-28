import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedSingularBridge
import OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicReferenceGlobalCohomology
import OAI.AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison
import OAI.AlgebraicTopology.Support.SingularSectionCohomology
import OAI.Algebra.Homology.DerivedCategoryConeNaturality

/-! # Supported Open Unit -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SupportedOpenUnit

noncomputable section

section

/-! # Relative cochains enter the original supported resolution by the actual unit -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable (R : Type) [Field R] (Y : TopCat.{0})

local notation "F" => forget₂ (ModuleCat R) AddCommGrpCat
local notation "FN" => Functor.mapHomologicalComplex (F) (ComplexShape.up ℕ)
local notation "Γ" => OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
local notation "ΓN" => Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)
local notation "P" => OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R Y
local notation "A" => ModuleCat.of R R

/-- The original supported section complex before the canonical integer extension. -/
def originalSupportedSingularGlobalComplexNat (O : Opens Y) : CochainComplex AddCommGrpCat ℕ :=
  (ΓN).obj (((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside Y O).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (P))

set_option backward.isDefEq.respectTransparency false in
/-- Taking genuine top-open sections of the support comparison. -/
def supportedSingularGlobalBridgeIso (O : Opens Y) :
    (FN).obj (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections (A) Y O ⊤) ≅
      originalSupportedSingularGlobalComplexNat R Y O :=
  (ΓN).mapIso (SupportedSingularBridge.supportedSingularComplexBridgeIso R Y O)

/-- Forgetting support on the unchanged original sheaf-cochain model. -/
def originalSupportedSingularGlobalInclusionNat (O : Opens Y) :
    originalSupportedSingularGlobalComplexNat R Y O ⟶
      AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R Y :=
  (ΓN).map (((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y O).mapHomologicalComplex
    (ComplexShape.up ℕ)).app (P))

/-- The actual relative-to-supported unit followed by actual chain evaluation. -/
def nativeRelativeToOriginalSupportedGlobal (O : Opens Y) :
    (FN).obj (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (A) Y (O : Set Y)) ⟶
      originalSupportedSingularGlobalComplexNat R Y O :=
  (FN).map (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (A) Y O) ≫
    (supportedSingularGlobalBridgeIso R Y O).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The supported unit retains precisely the actual ordinary sheafification unit. -/
theorem nativeRelativeToOriginalSupportedGlobal_inclusion (O : Opens Y) :
    nativeRelativeToOriginalSupportedGlobal R Y O ≫
        originalSupportedSingularGlobalInclusionNat R Y O =
      (FN).map (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (A) Y (O : Set Y)) ≫
        (FN).map (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (A) Y) ≫
          (IntrinsicReferenceGlobalCohomology.nativeSingularGlobalSheafBridgeIso R Y).hom := by
  dsimp only [nativeRelativeToOriginalSupportedGlobal, supportedSingularGlobalBridgeIso,
    originalSupportedSingularGlobalInclusionNat, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, SupportedSingularBridge.supportedSingularComplexBridgeIso_inclusion,
    Functor.map_comp, ← Category.assoc]
  change ((FN).map (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (A) Y O) ≫
      (FN).map (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (A) Y O ⊤)) ≫
        (IntrinsicReferenceGlobalCohomology.nativeSingularGlobalSheafBridgeIso R Y).hom = _
  rw [← Functor.map_comp,
    AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections_inclusion, Functor.map_comp]
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- On a metrizable space the actual supported unit is a quasi-isomorphism. -/
theorem quasiIso_nativeRelativeToOriginalSupportedGlobal [CharZero R] [MetrizableSpace Y]
    (O : Opens Y) : QuasiIso (nativeRelativeToOriginalSupportedGlobal R Y O) := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafGlobalSections_of_metrizable
    R Y O
  unfold nativeRelativeToOriginalSupportedGlobal
  infer_instance

end

/-! # The actual open relative-cochain unit and the original restriction cone -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (Y : TopCat.{0}) (U V : Opens Y)

local notation "F" => forget₂ (ModuleCat ℚ) AddCommGrpCat
local notation "FI" => Functor.mapHomologicalComplex (F) (ComplexShape.up ℤ)
local notation "P" => OAI.AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ Y
local notation "K" => OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex Y

/-- The sheafification unit, evaluated before the canonical extension by zero. -/
def originalOpenRawToIntegerSections (W : Opens Y) :
    (AlgebraicTopology.Singular.SheafCochainOpenSections.openRawSingularCochainComplex ℚ Y W).extend ComplexShape.embeddingUpNat ⟶
      ((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y W).mapHomologicalComplex (.up ℤ)).obj (K) :=
  HomologicalComplex.extendMap (AlgebraicTopology.Singular.SheafCochainOpenSections.openRawToSingularCochainSheafComplex ℚ Y W)
    ComplexShape.embeddingUpNat ≫
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y W) (P)
        ComplexShape.embeddingUpNat).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual unit commutes with restriction in integer degrees. -/
theorem originalOpenRawToIntegerSections_naturality {W W' : Opens Y} (i : W' ⟶ W) :
    HomologicalComplex.extendMap (AlgebraicTopology.Singular.SheafCochainOpenSections.openRawSingularRestriction ℚ Y i)
        ComplexShape.embeddingUpNat ≫ originalOpenRawToIntegerSections Y W' =
      originalOpenRawToIntegerSections Y W ≫ AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction Y (.up ℤ) (K) i := by
  unfold originalOpenRawToIntegerSections
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    ← AlgebraicTopology.Singular.SheafCochainTop.openSingularSheafRestriction_naturality, HomologicalComplex.extendMap_comp, Category.assoc]
  rw [Category.assoc]
  apply congrArg (fun g => HomologicalComplex.extendMap
    (AlgebraicTopology.Singular.SheafCochainOpenSections.openRawToSingularCochainSheafComplex ℚ Y W) ComplexShape.embeddingUpNat ≫ g)
  apply (cancel_mono (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso
    (AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y W') (P) ComplexShape.embeddingUpNat).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc]
  change HomologicalComplex.extendMap (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction Y (.up ℕ) (P) i)
      ComplexShape.embeddingUpNat =
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y W) (P)
      ComplexShape.embeddingUpNat).inv ≫
    AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction Y (.up ℤ) ((P).extend ComplexShape.embeddingUpNat) i ≫
    (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y W') (P)
      ComplexShape.embeddingUpNat).hom
  rw [AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction_extend, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The same unit on the actual algebraic dual of the singular chain complex. -/
def originalOpenDualToIntegerSections (W : Opens Y) :
    (FI).obj ((Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (AlgebraicTopology.Singular.Cohomology.SingularChainComplex ℚ (TopCat.of W))).extend
      ComplexShape.embeddingUpNat) ⟶
      ((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y W).mapHomologicalComplex (.up ℤ)).obj (K) :=
  (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularCochainComplexIntIsoDual ℚ Y W).inv ≫
    originalOpenRawToIntegerSections Y W

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chain-dual evaluation comparison preserves the actual inclusion restriction. -/
theorem originalOpenDualToIntegerSections_restriction {W W' : Opens Y} (i : W' ⟶ W) :
    (FI).map (AlgebraicTopology.Singular.RelativeCochainCone.relativeCochainRestrictionInt ℚ (AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair Y i)) ≫
        originalOpenDualToIntegerSections Y W' =
      originalOpenDualToIntegerSections Y W ≫ AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction Y (.up ℤ) (K) i := by
  apply (cancel_epi (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularCochainComplexIntIsoDual ℚ Y W).hom).mp
  unfold originalOpenDualToIntegerSections
  rw [← Category.assoc, ← AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionInt_transport,
    Category.assoc, Iso.hom_inv_id_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact originalOpenRawToIntegerSections_naturality Y i

/-- The unchanged relative singular short complex, with its scalars forgotten. -/
def originalOpenRelativeShortComplex : ShortComplex (CochainComplex AddCommGrpCat ℤ) :=
  (AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt ℚ
    (AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair Y (Opens.infLELeft V U))).map (FI)

/-- The unchanged supported sheaf-section short complex. -/
def originalOpenSupportShortComplex : ShortComplex (CochainComplex AddCommGrpCat ℤ) :=
  AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U V (K)

set_option backward.isDefEq.respectTransparency false in
/-- The ambient actual chain-dual-to-sheaf unit. -/
def originalOpenSupportUnitAmbient :
    (originalOpenRelativeShortComplex Y U V).X₂ ⟶
      (originalOpenSupportShortComplex Y U V).X₂ :=
  originalOpenDualToIntegerSections Y V

set_option backward.isDefEq.respectTransparency false in
/-- The complement unit followed by the actual intersection identification. -/
def originalOpenSupportUnitComplement :
    (originalOpenRelativeShortComplex Y U V).X₃ ⟶
      (originalOpenSupportShortComplex Y U V).X₃ :=
  originalOpenDualToIntegerSections Y (V ⊓ U) ≫
    (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsIntersectionIso Y U V (K)).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- These two actual units form a restriction square. -/
theorem originalOpenSupportUnit_restriction :
    (originalOpenRelativeShortComplex Y U V).g ≫ originalOpenSupportUnitComplement Y U V =
      originalOpenSupportUnitAmbient Y U V ≫ (originalOpenSupportShortComplex Y U V).g := by
  apply (cancel_mono (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsIntersectionIso Y U V (K)).hom).mp
  dsimp only [originalOpenSupportUnitComplement, originalOpenSupportUnitAmbient,
    originalOpenSupportShortComplex]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsIntersectionIso_restriction]
  exact originalOpenDualToIntegerSections_restriction Y (Opens.infLELeft V U)

set_option backward.isDefEq.respectTransparency false in
/-- The actual unit on the supported kernel, obtained from its kernel universal property. -/
def originalOpenSupportUnit [T2Space Y] [∀ W : Opens Y, ParacompactSpace W] :
    originalOpenRelativeShortComplex Y U V ⟶ originalOpenSupportShortComplex Y U V :=
  let hT := AlgebraicTopology.Support.FlasqueComparison.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque
    Y U V (K) (fun _ => inferInstance)
  let f := (originalOpenRelativeShortComplex Y U V).f ≫ originalOpenSupportUnitAmbient Y U V
  let hf : f ≫ (originalOpenSupportShortComplex Y U V).g = 0 := by
    dsimp only [f]
    rw [Category.assoc, ← originalOpenSupportUnit_restriction, ← Category.assoc,
      ShortComplex.zero, zero_comp]
  { τ₁ := hT.fIsKernel.lift (KernelFork.ofι f hf)
    τ₂ := originalOpenSupportUnitAmbient Y U V
    τ₃ := originalOpenSupportUnitComplement Y U V
    comm₁₂ := by
      exact hT.fIsKernel.fac (KernelFork.ofι f hf) WalkingParallelPair.zero
    comm₂₃ := (originalOpenSupportUnit_restriction Y U V).symm }

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SupportedOpenUnit
