import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointProjectiveCoefficientNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.PointNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingSectionsFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentedGroupCoordinateTransport

/-! # Relative Coordinate Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RelativeCoordinateTransport

noncomputable section

/-! Affine coordinate changes agree with the original relative projective
coordinate changes after the actual spectrum/global-sections comparison.
Thus their action on O(1), bounded group graphs, and ordered projective
points uses the original relative projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v

private theorem pointCoordinateBaseChangeEquiv_ringEquiv_cancel
    {R A : Type u} [CommRing R] [CommRing A] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (c : R ≃+* A) (T : (ι → R) ≃ₗ[R] (ι → R)) :
    PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv c.symm.toRingHom (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv c.toRingHom T) = T := by
  apply LinearEquiv.ext
  intro x
  calc
    _ = PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv c.symm.toRingHom
        (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv c.toRingHom T) (fun i => c.symm (c (x i))) :=
      congrArg (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv c.symm.toRingHom
        (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv c.toRingHom T))
        (funext fun i => (c.symm_apply_apply (x i)).symm)
    _ = fun i => c.symm (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv c.toRingHom T (fun j => c (x j)) i) :=
      PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv_apply_map c.symm.toRingHom _ _
    _ = fun i => c.symm (c (T x i)) :=
      congrArg (fun y i => c.symm (y i)) (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv_apply_map c.toRingHom T x)
    _ = T x := funext fun i => c.symm_apply_apply _

variable {C : Type u} [CommRing C] {n : ℕ}

def affinePointCoordinateRelativeIso
    (T : (Fin (n + 1) → C) ≃ₗ[C] (Fin (n + 1) → C)) :
    Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n ≅ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n :=
  Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n (Spec (.of C))
    (Dual.CoordinateTransform.pointCoordinateCoefficientTransform
      (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv (Scheme.ΓSpecIso (.of C)).inv.hom T)).symm

theorem affinePointCoordinateRelativeIso_chart
    (T : (Fin (n + 1) → C) ≃ₗ[C] (Fin (n + 1) → C)) :
    (PointCoordinateProjectiveAction.pointCoordinateProjectiveIso T).hom ≫ (RelativeProjective.TwistingSectionsFinite.identityAffineProjectiveChartIso (R := C) (n := n)).hom =
      (RelativeProjective.TwistingSectionsFinite.identityAffineProjectiveChartIso (R := C) (n := n)).hom ≫ (affinePointCoordinateRelativeIso T).hom := by
  let c := (Scheme.ΓSpecIso (.of C)).symm.commRingCatIsoToRingEquiv
  let V := PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv c.toRingHom T
  let q := RelativeProjective.TwistingSectionsFinite.identityAffineProjectiveChartIso (R := C) (n := n)
  let a := affinePointCoordinateRelativeIso T
  let p := RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection (Spec (.of C)) n
  have hV : PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv c.symm.toRingHom V = T :=
    pointCoordinateBaseChangeEquiv_ringEquiv_cancel c T
  have hN := PointProjectiveCoefficientNaturality.pointCoordinateProjectiveIso_coefficient_natural c.symm.toRingHom V
  rw [hV] at hN
  have hq : q.hom.left ≫ p = Projective.CoefficientFunctoriality.polynomialProjectiveMap (Scheme.ΓSpecIso (.of C)).hom n := by
    change AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n ≫
      Limits.pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(Spec (.of C), ⊤) n).hom
        (Spec (.of C)).toSpecΓ = _
    simpa only [AffineProjective.Charts.affinePointCoefficients, Scheme.Hom.id_appTop, Category.id_comp] using
      (AffineProjective.Charts.affineProjectiveChartMap_fst (𝟙 (Spec (.of C))) n)
  have ha : a.hom.left ≫ p = p ≫ (PointCoordinateProjectiveAction.pointCoordinateProjectiveIso V).hom.left :=
    Pullback.Comparisons.overPullback_map_left_fst (PointCoordinateProjectiveAction.pointCoordinateProjectiveIso V).hom (Spec (.of C)).toSpecΓ
  apply Over.OverMorphism.ext
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback (Spec (.of C)) n).hom_ext
  · change ((PointCoordinateProjectiveAction.pointCoordinateProjectiveIso T).hom.left ≫ q.hom.left) ≫ p =
      (q.hom.left ≫ a.hom.left) ≫ p
    calc
      _ = (PointCoordinateProjectiveAction.pointCoordinateProjectiveIso T).hom.left ≫
          Projective.CoefficientFunctoriality.polynomialProjectiveMap (Scheme.ΓSpecIso (.of C)).hom n := by rw [Category.assoc, hq]
      _ = Projective.CoefficientFunctoriality.polynomialProjectiveMap (Scheme.ΓSpecIso (.of C)).hom n ≫
          (PointCoordinateProjectiveAction.pointCoordinateProjectiveIso V).hom.left := hN
      _ = (q.hom.left ≫ a.hom.left) ≫ p := by
        rw [Category.assoc, ha, ← Category.assoc, hq]
  · exact ((PointCoordinateProjectiveAction.pointCoordinateProjectiveIso T).hom ≫ q.hom).w.trans (q.hom ≫ a.hom).w.symm

variable {ι : Type v} (v w : ι → Fin (n + 1) → C) (h : Configuration.ProjectiveTransport.ConfigurationFrameRelated v w)

def affineConfigurationRelativeIso :
    Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n ≅ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n :=
  affinePointCoordinateRelativeIso h.choose

theorem affineConfigurationRelativeIso_chart :
    (Configuration.ProjectiveTransport.configurationProjectiveTransport v w h).hom ≫ (RelativeProjective.TwistingSectionsFinite.identityAffineProjectiveChartIso (R := C) (n := n)).hom =
      (RelativeProjective.TwistingSectionsFinite.identityAffineProjectiveChartIso (R := C) (n := n)).hom ≫ (affineConfigurationRelativeIso v w h).hom :=
  affinePointCoordinateRelativeIso_chart h.choose

theorem affineConfigurationRelativeIso_point (z : ι)
    (hv : ∀ x : Spec (.of C), ∃ i,
      x ∈ (Spec (.of C)).basicOpen ((Scheme.ΓSpecIso (.of C)).inv (v z i)))
    (hw : ∀ x : Spec (.of C), ∃ i,
      x ∈ (Spec (.of C)).basicOpen ((Scheme.ΓSpecIso (.of C)).inv (w z i))) :
    Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (fun i => (Scheme.ΓSpecIso (.of C)).inv (v z i)) hv ≫
        (affineConfigurationRelativeIso v w h).hom =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (fun i => (Scheme.ΓSpecIso (.of C)).inv (w z i)) hw := by
  let S := Spec (.of C)
  let c := (Scheme.ΓSpecIso (.of C)).inv.hom
  let V := PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv c h.choose
  let u := Units.map c.toMonoidHom (h.choose_spec.choose z)
  let vz := fun i => c (v z i)
  let wz := fun i => c (w z i)
  have hc (i : Fin (n + 1)) : wz i = (u : Γ(S, ⊤)) * V vz i := by
    change c (w z i) = c (h.choose_spec.choose z) *
      PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv c h.choose (fun j => c (v z j)) i
    rw [PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv_apply_map]
    exact (congrArg c (congrFun (h.choose_spec.choose_spec z) i)).trans (map_mul c _ _)
  have hV : ∀ x : S, ∃ i, x ∈ S.basicOpen (V vz i) := by
    intro x
    obtain ⟨i, hi⟩ := hw x
    change x ∈ S.basicOpen (wz i) at hi
    rw [hc i, S.basicOpen_mul] at hi
    exact ⟨i, hi.2⟩
  change Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint vz hv ≫
    (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S (Dual.CoordinateTransform.pointCoordinateCoefficientTransform V).symm).hom =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint wz hw
  exact (Scalar.ProjectiveCoordinateAction.scalarCoordinateProjectivePoint_linear_action S vz V hv hV).trans
    (ProjectiveFrame.PointNormalization.scalarCoordinateProjectivePoint_eq_of_unit_mul S wz (V vz) u hc hw hV).symm

variable {X Y : Over (Spec (.of C))}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n)
    (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left] (e : X ≅ Y)
    (he : e.hom ≫ j ≫ (RelativeProjective.TwistingSectionsFinite.identityAffineProjectiveChartIso (R := C) (n := n)).inv =
      i ≫ (RelativeProjective.TwistingSectionsFinite.identityAffineProjectiveChartIso (R := C) (n := n)).inv ≫
        (Configuration.ProjectiveTransport.configurationProjectiveTransport v w h).hom)

include he

omit [IsClosedImmersion (Over.Hom.left i)] [IsClosedImmersion (Over.Hom.left j)] in
theorem affineConfigurationRelativeIso_embedding :
    e.hom ≫ j = i ≫ (affineConfigurationRelativeIso v w h).hom := by
  let q := RelativeProjective.TwistingSectionsFinite.identityAffineProjectiveChartIso (R := C) (n := n)
  have hq := affineConfigurationRelativeIso_chart v w h
  have hi : q.inv ≫ (Configuration.ProjectiveTransport.configurationProjectiveTransport v w h).hom ≫ q.hom =
      (affineConfigurationRelativeIso v w h).hom := by
    rw [hq, q.inv_hom_id_assoc]
  have H : (e.hom ≫ j ≫ q.inv) ≫ q.hom =
      (i ≫ q.inv ≫ (Configuration.ProjectiveTransport.configurationProjectiveTransport v w h).hom) ≫ q.hom :=
    congrArg (fun f : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace C n => f ≫ q.hom) he
  simpa only [Category.assoc, q.inv_hom_id, Category.comp_id, hi] using H

def affineConfigurationEmbeddingTwistingIso :
    ((((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of C)) n).pullback j.left).pullback e.hom.left).sheaf) ≅
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of C)) n).pullback i.left).sheaf :=
  PresentedGroupCoordinateTransport.projectiveEmbeddingCoordinateTwistingIso i j e
    (Dual.CoordinateTransform.pointCoordinateCoefficientTransform
      (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv (Scheme.ΓSpecIso (.of C)).inv.hom h.choose)).symm
    (affineConfigurationRelativeIso_embedding v w h i j e he)

variable [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]
    [Flat Y.hom] [LocallyOfFinitePresentation Y.hom] [IsSeparated Y.hom]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds.ofAffineConfiguration
    (D : FamilyGroup.Operations.FamilyGroupOperations X) (Hm Hi : Polynomial ℚ)
    (hD : D.ProjectiveGraphBounds (⟨n, i, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation X) Hm Hi) :
    (D.ofIso e).ProjectiveGraphBounds (⟨n, j, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation Y) Hm Hi :=
  FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds.ofBundleIso
    (⟨n, i, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation X)
    (⟨n, j, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation Y) e
    (affineConfigurationEmbeddingTwistingIso v w h i j e he) D Hm Hi hD

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RelativeCoordinateTransport
