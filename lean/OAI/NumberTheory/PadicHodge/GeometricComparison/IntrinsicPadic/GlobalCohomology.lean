import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReferenceHomologyIsomorphisms
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedCommonGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedCechPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinementOneAliases
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReferenceConeOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinementConeCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.RefinedGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CohomologyNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Refinement

/-! # Global Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology

noncomputable section

/-! Actual geometric pullback on the common paired Cech complex
agrees with the original native bounded crystalline comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  (I₁ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n))
  (I₂ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n))

local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂

local instance source_products (m : ℕ) (t : Fin (m + 1) → Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X₁) :
    PreservesLimit (Discrete.functor (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁ ∘ t))
      (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₁ Y₁ f₁) := by
  dsimp only [SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens]
  infer_instance
local instance target_products (m : ℕ) (t : Fin (m + 1) → Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X₂) :
    PreservesLimit (Discrete.functor (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂ ∘ t))
      (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X₂ Y₂ f₂) := by
  dsimp only [SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens]
  infer_instance

local instance source_edge_epi : Epi
    (CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_original p f₁ n I₁) := by
  let : IsIso (CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_original p f₁ n I₁) :=
    ReferenceHomologyIsomorphisms.IntrinsicPadicGeometricReferenceHomologyIsomorphisms.source p f₁ n I₁
  infer_instance
local instance target_edge_epi : Epi
    (CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_original p f₂ n I₂) := by
  let : IsIso (CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_original p f₂ n I₂) :=
    ReferenceHomologyIsomorphisms.IntrinsicPadicGeometricReferenceHomologyIsomorphisms.target p f₂ n I₂
  infer_instance

def sourceMap := HomologyMaps.IntrinsicPadicGeometricRawHomologyMaps.sourceRawRefinement p u f₁ n I₁
def targetMap := HomologyMaps.IntrinsicPadicGeometricRawHomologyMaps.targetRawRefinement p u f₂ n I₂
def geometricMap := TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.injectiveHOne p u v f₁ f₂ hsquare n I₁ I₂

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_edge_homology : CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_original p f₁ n I₁ ≫
    sourceMap p u f₁ n I₁ = CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.source_common p u f₁ n I₁ :=
  (congrArg (fun a => CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_original p f₁ n I₁ ≫ a)
    (RefinementOneAliases.IntrinsicPadicGeometricRefinementHOneAliases.source p u f₁ n I₁).symm).trans
      (ReferenceConeOne.IntrinsicPadicGeometricReferenceConeHOne.source_cone p u f₁ n I₁)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_edge_homology : CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_original p f₂ n I₂ ≫
    targetMap p u f₂ n I₂ = CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.target_common p u f₂ n I₂ :=
  (congrArg (fun a => CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_original p f₂ n I₂ ≫ a)
    (RefinementOneAliases.IntrinsicPadicGeometricRefinementHOneAliases.target p u f₂ n I₂).symm).trans
      (ReferenceConeOne.IntrinsicPadicGeometricReferenceConeHOne.target_cone p u f₂ n I₂)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem geometric_edge_homology : CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.target_common p u f₂ n I₂ ≫
    geometricMap p u v f₁ f₂ hsquare n I₁ I₂ =
      TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.globalHOne p v n I₁ I₂ ≫
        CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.source_common p u f₁ n I₁ :=
  by
    rw [← ReferenceConeOne.IntrinsicPadicGeometricTypedCommonHomologyCoordinates.target_homology,
      ← ReferenceConeOne.IntrinsicPadicGeometricTypedCommonHomologyCoordinates.source_homology]
    exact TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.cone_homology p u v f₁ f₂ hsquare n I₁ I₂

/- These are the original maps, with the geometric cohomology objects
fixed before applying categorical cancellation. -/
def sourceOriginalComparison :
    (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceOld p f₁ n I₁).homology 1 ⟶
      TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.global p n (Y₁ := Y₁) :=
  (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.homologyIso p X₁ Y₁ f₁ n I₁ 1).hom

def targetOriginalComparison :
    (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetOld p f₂ n I₂).homology 1 ⟶
      TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.global p n (Y₁ := Y₂) :=
  (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.homologyIso p X₂ Y₂ f₂ n I₂ 1).hom

def targetSectionComparison :
    (ConeSectionData.IntrinsicPadicGeometricConeSectionData.targetGlobal p n I₂).homology 1 ⟶
      TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.global p n (Y₁ := Y₂) :=
  (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso w₂ n I₂ 1).hom

def crystallinePullback : TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.global p n (Y₁ := Y₂) ⟶
    TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.global p n (Y₁ := Y₁) :=
  ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback v.left
    (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n 1)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_original_homology :
    CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_original p f₁ n I₁ ≫
      sourceOriginalComparison p f₁ n I₁ = TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.globalMap p n I₁ :=
  TypedReferenceGlobalEdge.IntrinsicPadicTypedReferenceGlobalEdge.homology p X₁ Y₁ f₁ n I₁ 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_original_homology :
    CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_original p f₂ n I₂ ≫
      targetOriginalComparison p f₂ n I₂ = targetSectionComparison p n I₂ :=
  TypedReferenceGlobalEdge.IntrinsicPadicTypedReferenceGlobalEdge.homology p X₂ Y₂ f₂ n I₂ 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem global_pullback_homology :
    TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.globalHOne p v n I₁ I₂ ≫
      TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.globalMap p n I₁ =
    targetSectionComparison p n I₂ ≫ crystallinePullback p v n :=
  Bounded.OpenCohomology.BoundedGeometricOpenCohomology.homology v.left
    (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n I₂ I₁ 1

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem source_comparison :
    sourceMap p u f₁ n I₁ ≫ TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.comparison p u f₁ n I₁ =
      sourceOriginalComparison p f₁ n I₁ :=
  RefinedGlobal.RefinedGlobalConeNaturality.source
    (e₁ := CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.source_original p f₁ n I₁)
    (r₁ := sourceMap p u f₁ n I₁)
    (p₁ := CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.source_common p u f₁ n I₁)
    (i₁ := sourceOriginalComparison p f₁ n I₁)
    (h := TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.comparison p u f₁ n I₁)
    (j₁ := TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.globalMap p n I₁)
    (source_edge_homology p u f₁ n I₁)
    (TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.homology p u f₁ n I₁)
    (source_original_homology p f₁ n I₁)

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem target_comparison : targetMap p u f₂ n I₂ ≫ geometricMap p u v f₁ f₂ hsquare n I₁ I₂ ≫
    TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.comparison p u f₁ n I₁ =
      targetOriginalComparison p f₂ n I₂ ≫ crystallinePullback p v n :=
  RefinedGlobal.RefinedGlobalConeNaturality.target
    (e₂ := CommonHomologyMaps.IntrinsicPadicGeometricConeHomologyMaps.target_original p f₂ n I₂)
    (r₂ := targetMap p u f₂ n I₂)
    (p₁ := CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.source_common p u f₁ n I₁)
    (p₂ := CommonHomologyMaps.IntrinsicPadicGeometricCommonHomologyMaps.target_common p u f₂ n I₂)
    (a := TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.globalHOne p v n I₁ I₂)
    (b := geometricMap p u v f₁ f₂ hsquare n I₁ I₂)
    (g := crystallinePullback p v n)
    (i₂ := targetOriginalComparison p f₂ n I₂)
    (h := TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.comparison p u f₁ n I₁)
    (j₁ := TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.globalMap p n I₁)
    (j₂ := targetSectionComparison p n I₂)
    (target_edge_homology p u f₂ n I₂)
    (geometric_edge_homology p u v f₁ f₂ hsquare n I₁ I₂)
    (TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.homology p u f₁ n I₁)
    (global_pullback_homology p v n I₁ I₂)
    (target_original_homology p f₂ n I₂)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology
