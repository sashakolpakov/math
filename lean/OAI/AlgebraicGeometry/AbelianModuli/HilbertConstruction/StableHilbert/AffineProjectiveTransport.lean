import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineProjectiveEmbedding

/-! # Affine Projective Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineProjectiveTransport

noncomputable section

/-! The original affine overlap isomorphism preserves the twisting line
of the native universal Hilbert presentation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private abbrev nativeFamilyPresentation
    {B : Scheme.{u}} {n : ℕ} {H : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily B n H) : Projective.ProjectivePresentations.ProjectivePresentation F.family.scheme :=
  ⟨n, F.family.inclusion, inferInstance⟩

private def nativeEmbedding
    {B S : Scheme.{u}} {n : ℕ} {H : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily B n H) (f : S ⟶ B) :
    (Over.pullback f).obj F.family.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n :=
  (Over.pullback f).map F.family.inclusion ≫ (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv

private theorem nativeFamily_ampleSheaf_eq
    {B S : Scheme.{u}} {n : ℕ} {H : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily B n H) (f : S ⟶ B) :
    ((nativeFamilyPresentation F).baseChange f).ampleLineBundle.sheaf =
      (Scheme.Modules.pullback (nativeEmbedding F f).left).obj
        (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf := rfl

private def transportPullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M M' : Y.Modules} {N N' : X.Modules}
    (hM : M = M') (hN : N = N') (e : (Scheme.Modules.pullback f).obj M' ≅ N') :
    (Scheme.Modules.pullback f).obj M ≅ N :=
  (Scheme.Modules.pullback f).mapIso (eqToIso hM) ≪≫ e ≪≫ (eqToIso hN).symm

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

private def nativeCoordinateTwistingIso
    {B S : Scheme.{u}} {n : ℕ} {H : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily B n H) (f g : S ⟶ B)
    (e : (Over.pullback f).obj F.family.scheme ≅ (Over.pullback g).obj F.family.scheme)
    (z : (Fin (n + 1) →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) →₀ Γ(S, ⊤)))
    (h : e.hom.left ≫ (nativeEmbedding F g).left =
      (nativeEmbedding F f).left ≫ (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S z).hom.left) :
    (Scheme.Modules.pullback e.hom.left).obj
      ((Scheme.Modules.pullback (nativeEmbedding F g).left).obj
        (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf) ≅
      (Scheme.Modules.pullback (nativeEmbedding F f).left).obj
        (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf := by
  let i := nativeEmbedding F f
  let j := nativeEmbedding F g
  let : IsClosedImmersion i.left :=
    @IsClosedImmersion.comp _ _ _ _ _ (Projective.PresentationBaseChange.overPullback_map_closed F.family.inclusion f)
      (Grassmann.ProjectivePresentation.overIso_closedImmersion (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).symm)
  let : IsClosedImmersion j.left :=
    @IsClosedImmersion.comp _ _ _ _ _ (Projective.PresentationBaseChange.overPullback_map_closed F.family.inclusion g)
      (Grassmann.ProjectivePresentation.overIso_closedImmersion (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso g n).symm)
  exact rawCoordinateTwistingIso i j e z h

namespace StableHilbertAffineTransport

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    {n m : ℕ} (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {f : Spec (.of C) ⟶ Spec (.of R)}

variable (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)

def familyIso_twisting :
    ((((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
        (AffineProjectiveEmbedding.StableHilbertAffineTransport.rightPoint R i D H hH hD j k b).left).ampleLineBundle.pullback
      (AffineProjectiveEmbedding.StableHilbertAffineTransport.familyIso R i D H hH hD j k b).hom.left).sheaf) ≅
      ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
        (AffineProjectiveEmbedding.StableHilbertAffineTransport.leftPoint R i D H hH hD j k b).left).ampleLineBundle.sheaf := by
  let x := b ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D H
  let h := StableChartFrames.stablePolynomialIntersection_frameRelated R i j k x
  let F := Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H
  exact transportPullbackIso (AffineProjectiveEmbedding.StableHilbertAffineTransport.familyIso R i D H hH hD j k b).hom.left
    (nativeFamily_ampleSheaf_eq F (AffineProjectiveEmbedding.StableHilbertAffineTransport.rightPoint R i D H hH hD j k b).left)
    (nativeFamily_ampleSheaf_eq F (AffineProjectiveEmbedding.StableHilbertAffineTransport.leftPoint R i D H hH hD j k b).left)
    (nativeCoordinateTwistingIso F
      (AffineProjectiveEmbedding.StableHilbertAffineTransport.leftPoint R i D H hH hD j k b).left (AffineProjectiveEmbedding.StableHilbertAffineTransport.rightPoint R i D H hH hD j k b).left
      (AffineProjectiveEmbedding.StableHilbertAffineTransport.familyIso R i D H hH hD j k b)
      (Dual.CoordinateTransform.pointCoordinateCoefficientTransform
        (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv (Scheme.ΓSpecIso (.of C)).inv.hom h.choose)).symm
      (AffineProjectiveEmbedding.StableHilbertAffineTransport.familyIso_native_embedding R i D H hH hD j k b))

end StableHilbertAffineTransport

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineProjectiveTransport
