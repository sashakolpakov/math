import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelReferenceRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.ParameterIsoDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting

/-! # Reference Normalized Line -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceNormalizedLine.StableHilbertLevelReferenceRecovery

noncomputable section

/-! The global stable overlap comparison preserves the actual
zero-normalized Hilbert line bundle. Raw O(1) compatibility is used only
on the affine tests where the actual coordinate change is available. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private def rawCoordinateTwistingIso
    {S : Scheme.{u}} {X Y : Over S} {n : ℕ}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (e : X ≅ Y)
    (z : (Fin (n + 1) →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) →₀ Γ(S, ⊤)))
    (h : e.hom.left ≫ j.left = i.left ≫ (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S z).hom.left) :
    (Scheme.Modules.pullback e.hom.left).obj
      ((Scheme.Modules.pullback j.left).obj (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf) ≅
      (Scheme.Modules.pullback i.left).obj (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf := by
  have he : e.hom ≫ j = i ≫ (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S z).hom := by
    apply Over.OverMorphism.ext
    exact h
  exact PresentedGroupCoordinateTransport.projectiveEmbeddingCoordinateTwistingIso i j e z he

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)

local notation "S₀" => Spec (CommRingCat.of R)
local notation "A₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S₀ n H g Hm Hi N
local notation "P₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S₀ n H g Hm Hi N
local notation "Mj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels
local notation "Mk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels
local notation "Fj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels
local notation "Fk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels
local notation "Hj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels
local notation "Hk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels
local notation "lj" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD
local notation "lk" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD

/-- On an affine overlap the original O(1) bundles themselves are
identified by the original coordinate change. -/
def affineTwistingIso
    {C : Type u} [CommRing C] [IsNoetherianRing C] {f : Spec (.of C) ⟶ S₀}
    (t : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : Over.mk f ⟶ Mj) (hu : u ≫ Hj = t ≫ lj)
    (v : Over.mk f ⟶ Mk) (hv : v ≫ Hk = t ≫ lk) :
    ((((P₀).baseChange (v ≫ Fk).left).ampleLineBundle).pullback
      (LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom.left).sheaf ≅
        ((P₀).baseChange (u ≫ Fj).left).ampleLineBundle.sheaf := by
  let x := t ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D H
  let h := StableChartFrames.stablePolynomialIntersection_frameRelated R i j k x
  let i₀ : ((A₀).pullback (u ≫ Fj).left).scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n :=
    ((P₀).baseChange (u ≫ Fj).left).embedding
  let j₀ : ((A₀).pullback (v ≫ Fk).left).scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n :=
    ((P₀).baseChange (v ≫ Fk).left).embedding
  let : IsClosedImmersion i₀.left := ((P₀).baseChange (u ≫ Fj).left).closedImmersion
  let : IsClosedImmersion j₀.left := ((P₀).baseChange (v ≫ Fk).left).closedImmersion
  exact rawCoordinateTwistingIso i₀ j₀
    (LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso R i D H hH hD g Hm Hi N labels j k t u hu v hv)
    (Dual.CoordinateTransform.pointCoordinateCoefficientTransform
      (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv (Scheme.ΓSpecIso (.of C)).inv.hom h.choose)).symm
    (LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.affine_embedding_left R i D H hH hD g Hm Hi N labels j k t u hu v hv)

private def affineTwistingIso_ring
    (C : CommRingCat.{u}) [IsNoetherianRing C] {f : Spec C ⟶ Spec (CommRingCat.of R)}
    (t : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : Over.mk f ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)
    (hu : u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels =
      t ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (v : Over.mk f ⟶ LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)
    (hv : v ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels =
      t ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) :
    ((((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange
      (v ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels).left).ampleLineBundle).pullback
      (LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom.left).sheaf ≅
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange
      (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left).ampleLineBundle.sheaf := by
  rcases C with ⟨C, instC⟩
  exact affineTwistingIso (C := C) (f := f) R i D H hH hD g Hm Hi N labels j k t u hu v hv

variable {T : Over (Spec (CommRingCat.of R))} [IsLocallyNoetherian T.left]
    (t : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)) (hu : u ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))
    (v : T ⟶ (LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)) (hv : v ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = t ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD))

/-- The normalized line compatibility is global; no global affine
coordinate matrix or unnormalized bundle isomorphism is assumed. -/
theorem normalized_class :
    Line.Bundles.LineBundle.pullbackClass (LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso (T := T) R i D H hH hD g Hm Hi N labels j k t u hu v hv).hom.left
      (Line.Bundles.LineBundle.classOf ((((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)).zeroNormalizedBundle ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).ampleLineBundle).pullback
        (pullback.fst ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)).scheme.hom (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left))) =
    Line.Bundles.LineBundle.classOf ((((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)).zeroNormalizedBundle ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).ampleLineBundle).pullback
      (pullback.fst ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)).scheme.hom (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left)) := by
  let C := T.left.affineOpenCover.openCover
  let c (a : C.I₀) := HilbertConstruction.Over.AffineCoverLifts.affineCoverOverMap T a
  have hu' (a : C.I₀) : (c a ≫ u) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) = (c a ≫ t) ≫ (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) :=
    (Category.assoc _ _ _).trans ((congrArg (fun f => c a ≫ f) hu).trans (Category.assoc _ _ _).symm)
  have hv' (a : C.I₀) : (c a ≫ v) ≫ (LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels) = (c a ≫ t) ≫ (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) :=
    (Category.assoc _ _ _).trans ((congrArg (fun f => c a ≫ f) hv).trans (Category.assoc _ _ _).symm)
  let ys (a : C.I₀) := ((c a ≫ u) ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left
  let zs (a : C.I₀) := ((c a ≫ v) ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left
  have hy (a : C.I₀) : C.f a ≫ (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left = ys a :=
    congrArg Over.Hom.left (Category.assoc (c a) u (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).symm
  have hz (a : C.I₀) : C.f a ≫ (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left = zs a :=
    congrArg Over.Hom.left (Category.assoc (c a) v (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).symm
  let e' (a : C.I₀) := LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso R i D H hH hD g Hm Hi N labels j k
    (c a ≫ t) (c a ≫ u) (hu' a) (c a ≫ v) (hv' a)
  apply ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)).zeroNormalizedParameter_class_of_openCover ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)) ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).ampleLineBundle
    (u ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)).left (v ≫ (LevelForgetful.StableHilbertFullLevel.toFullLevel R i k D H hH g Hm Hi N labels)).left (LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.iso (T := T) R i D H hH hD g Hm Hi N labels j k t u hu v hv)
    C ys zs hy hz e'
  · intro a
    exact LevelReferenceRecovery.StableHilbertFullLevelOriginalRecovery.natural R i D H hH hD g Hm Hi N labels j k t u hu v hv (c a) (hu' a) (hv' a)
  · intro a
    have : IsOpenImmersion (T.left.affineOpenCover.f a) :=
      inferInstanceAs (IsOpenImmersion (C.f a))
    let : IsNoetherianRing (T.left.affineOpenCover.X a) :=
      isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion (T.left.affineOpenCover.f a))
    have hE : Line.Bundles.LineBundle.pullbackClass (e' a).hom.left
        (Line.Bundles.LineBundle.classOf ((((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).baseChange (zs a)).ampleLineBundle)) =
      Line.Bundles.LineBundle.classOf ((((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).baseChange (ys a)).ampleLineBundle) :=
      Quotient.sound ⟨affineTwistingIso_ring R i D H hH hD g Hm Hi N labels j k (T.left.affineOpenCover.X a)
        (c a ≫ t) (c a ≫ u) (hu' a) (c a ≫ v) (hv' a)⟩
    have hY : Line.Bundles.LineBundle.classOf ((((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).baseChange (ys a)).ampleLineBundle) =
        Line.Bundles.LineBundle.classOf (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).ampleLineBundle.pullback (pullback.fst ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)).scheme.hom (ys a))) :=
      Quotient.sound ⟨((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).baseChangeTwistingBundleIso (ys a)⟩
    have hZ : Line.Bundles.LineBundle.classOf ((((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).baseChange (zs a)).ampleLineBundle) =
        Line.Bundles.LineBundle.classOf (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).ampleLineBundle.pullback (pullback.fst ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme (Spec (CommRingCat.of R)) n H g Hm Hi N)).scheme.hom (zs a))) :=
      Quotient.sound ⟨((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N)).baseChangeTwistingBundleIso (zs a)⟩
    exact (congrArg (Line.Bundles.LineBundle.pullbackClass (e' a).hom.left) hZ.symm).trans (hE.trans hY)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceNormalizedLine.StableHilbertLevelReferenceRecovery
