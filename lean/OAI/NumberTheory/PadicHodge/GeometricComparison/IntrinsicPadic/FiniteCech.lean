import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedIntegralOneCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.RefinedGlobalSquare

/-! # Finite Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FiniteCech.IntrinsicPadicGeometricFiniteCechComparison

noncomputable section

/-! The original finite-level integral Cech comparison is natural
on the actual common source cover under geometric pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  (I₁ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n))
  (I₂ : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Cover.IntrinsicPadicGeometricCover.pairs p u

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasLimitsOfSize.{0, 0, 2, 1}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasColimitsOfSize.{2, 1, 0, 0} R

/- Name the actual complex and module endpoints before forming composites.
All maps below are transparent definitions of the original maps. -/
def sourceTotal : CochainComplex (ModuleCat.{2} R) ℕ :=
  CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.total.{1, 2} R (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₁)
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₁ n))

def targetTotal : CochainComplex (ModuleCat.{2} R) ℕ :=
  CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.total.{1, 2} R (CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X₂)
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X₂ n))

def sourceFirst : (sourceTotal p (X₁ := X₁) n).homology 1 ⟶
    (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.sourceOld p f₁ n I₁).homology 1 :=
  TypedRefinement.IntrinsicPadicGeometricTypedComparisonRefinement.sourceOriginalHOne p f₁ hp₁ n I₁

def targetFirst : (targetTotal p (X₂ := X₂) n).homology 1 ⟶
    (GeometricCone.IntrinsicPadicGeometricConeTotalMaps.targetOld p f₂ n I₂).homology 1 :=
  TypedRefinement.IntrinsicPadicGeometricTypedComparisonRefinement.targetOriginalHOne p f₂ hp₂ n I₂

def sourceOriginal : (sourceTotal p (X₁ := X₁) n).homology 1 ⟶
    TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.global p n (Y₁ := Y₁) :=
  (IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne.homologyIso p X₁ Y₁ f₁ hp₁ n I₁).hom

def targetOriginal : (targetTotal p (X₂ := X₂) n).homology 1 ⟶
    TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.global p n (Y₁ := Y₂) :=
  (IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne.homologyIso p X₂ Y₂ f₂ hp₂ n I₂).hom

def sourceRefinement : (sourceTotal p (X₁ := X₁) n).homology 1 ⟶
    (TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.sourceIntegral p u n).homology 1 :=
  TypedRefinement.IntrinsicPadicGeometricTypedComparisonRefinement.sourceIntegralHOne p u n

def targetRefinement : (targetTotal p (X₂ := X₂) n).homology 1 ⟶
    (TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.targetIntegral p u n).homology 1 :=
  TypedRefinement.IntrinsicPadicGeometricTypedComparisonRefinement.targetIntegralHOne p u n

def commonComparison :
    (TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.sourceIntegral p u n).homology 1 ⟶
      TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.global p n (Y₁ := Y₁) :=
  TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.sourceComparisonHOne p u f₁ hp₁ n I₁ ≫
    TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.comparison p u f₁ n I₁

/- Isolate the original isoOfQuasiIsoAt H¹ factor from the refinement
and global naturality proofs. These identities unfold the actual isomorphism. -/
omit [IsSeparated Y₂.hom] in
theorem source_original_factor : sourceOriginal p f₁ hp₁ n I₁ =
    sourceFirst p f₁ hp₁ n I₁ ≫
      GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.sourceOriginalComparison p f₁ n I₁ := rfl

omit [IsSeparated Y₁.hom] in
theorem target_original_factor : targetOriginal p f₂ hp₂ n I₂ =
    targetFirst p f₂ hp₂ n I₂ ≫
      GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.targetOriginalComparison p f₂ n I₂ := rfl

omit [IsSeparated Y₂.hom] in
theorem source_refinement_square : sourceFirst p f₁ hp₁ n I₁ ≫
    GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.sourceMap p u f₁ n I₁ =
      sourceRefinement p u n ≫
        TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.sourceComparisonHOne p u f₁ hp₁ n I₁ :=
  TypedRefinement.IntrinsicPadicGeometricTypedComparisonRefinement.source p u f₁ hp₁ n I₁

omit [IsSeparated Y₁.hom] in
theorem target_refinement_square : targetFirst p f₂ hp₂ n I₂ ≫
    GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.targetMap p u f₂ n I₂ =
      targetRefinement p u n ≫
        TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.targetComparisonHOne p u f₂ hp₂ n I₂ :=
  TypedRefinement.IntrinsicPadicGeometricTypedComparisonRefinement.target p u f₂ hp₂ n I₂

omit [IsSeparated Y₂.hom] in
theorem source_factored : sourceFirst p f₁ hp₁ n I₁ ≫
    GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.sourceOriginalComparison p f₁ n I₁ =
      sourceRefinement p u n ≫ commonComparison p u f₁ hp₁ n I₁ :=
  RefinedGlobalSquare.RefinedComparisonGlobalSquare.source
    (sourceFirst p f₁ hp₁ n I₁)
    (GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.sourceMap p u f₁ n I₁)
    (GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.sourceOriginalComparison p f₁ n I₁)
    (sourceRefinement p u n)
    (TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.sourceComparisonHOne p u f₁ hp₁ n I₁)
    (TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.comparison p u f₁ n I₁)
    (source_refinement_square p u f₁ hp₁ n I₁)
    (GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.source_comparison p u f₁ n I₁)

omit [IsSeparated Y₂.hom] in
theorem source : sourceOriginal p f₁ hp₁ n I₁ =
    sourceRefinement p u n ≫ commonComparison p u f₁ hp₁ n I₁ :=
  (source_original_factor p f₁ hp₁ n I₁).trans (source_factored p u f₁ hp₁ n I₁)

def targetOriginalComposite : (targetTotal p (X₂ := X₂) n).homology 1 ⟶
    TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.global p n (Y₁ := Y₁) :=
  targetOriginal p f₂ hp₂ n I₂ ≫ GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.crystallinePullback p v n

omit [IsSeparated Y₁.hom] in
theorem target_original_composite_factor : targetOriginalComposite p v f₂ hp₂ n I₂ =
    targetFirst p f₂ hp₂ n I₂ ≫
      GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.targetOriginalComparison p f₂ n I₂ ≫
        GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.crystallinePullback p v n :=
  (congrArg (fun a : (targetTotal p (X₂ := X₂) n).homology 1 ⟶
      TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.global p n (Y₁ := Y₂) =>
    a ≫ GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.crystallinePullback p v n)
    (target_original_factor p f₂ hp₂ n I₂)).trans (Category.assoc _ _ _)

include hsquare in
theorem target_factored : targetFirst p f₂ hp₂ n I₂ ≫
    GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.targetOriginalComparison p f₂ n I₂ ≫
      GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.crystallinePullback p v n =
    targetRefinement p u n ≫ TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.integralHOne p u n ≫
      commonComparison p u f₁ hp₁ n I₁ :=
  RefinedGlobalSquare.RefinedComparisonGlobalSquare.target
    (targetFirst p f₂ hp₂ n I₂)
    (GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.targetMap p u f₂ n I₂)
    (GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.targetOriginalComparison p f₂ n I₂)
    (GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.crystallinePullback p v n)
    (targetRefinement p u n)
    (TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.targetComparisonHOne p u f₂ hp₂ n I₂)
    (GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.geometricMap p u v f₁ f₂ hsquare n I₁ I₂)
    (TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.integralHOne p u n)
    (TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.sourceComparisonHOne p u f₁ hp₁ n I₁)
    (TypedCommonGlobal.IntrinsicPadicGeometricTypedCommonGlobal.comparison p u f₁ n I₁)
    (target_refinement_square p u f₂ hp₂ n I₂)
    (TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.homology p u v f₁ f₂ hp₁ hp₂ hsquare n I₁ I₂)
    (GlobalCohomology.IntrinsicPadicGeometricGlobalCohomology.target_comparison p u v f₁ f₂ hsquare n I₁ I₂)

theorem target_integral_coordinates :
    targetRefinement p u n ≫ TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.integralHOne p u n ≫
      commonComparison p u f₁ hp₁ n I₁ =
    targetRefinement p u n ≫ CechHomotopy.IntrinsicPadicGeometricCechHomotopy.sourceHOneMap p u n ≫
      commonComparison p u f₁ hp₁ n I₁ :=
  congrArg (fun a : (TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.targetIntegral p u n).homology 1 ⟶
      (TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.sourceIntegral p u n).homology 1 =>
    targetRefinement p u n ≫ a ≫ commonComparison p u f₁ hp₁ n I₁)
    (TypedIntegralOneCoordinates.IntrinsicPadicGeometricTypedIntegralHOneCoordinates.homology p u n)

include hsquare in
theorem target : targetOriginalComposite p v f₂ hp₂ n I₂ =
    targetRefinement p u n ≫ CechHomotopy.IntrinsicPadicGeometricCechHomotopy.sourceHOneMap p u n ≫
      commonComparison p u f₁ hp₁ n I₁ :=
  (target_original_composite_factor p v f₂ hp₂ n I₂).trans
    ((target_factored p u v f₁ f₂ hp₁ hp₂ hsquare n I₁ I₂).trans
      (target_integral_coordinates p u f₁ hp₁ n I₁))

/- Compare each full compiled theorem type against its original literal
equation in the natural binder context. Transparent names add no premises. -/

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FiniteCech.IntrinsicPadicGeometricFiniteCechComparison
