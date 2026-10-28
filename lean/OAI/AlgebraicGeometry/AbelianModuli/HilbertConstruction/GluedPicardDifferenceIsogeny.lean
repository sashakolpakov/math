import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GluedPicardDifferenceMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.MorphismPropertyOpenDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedDifferenceDualData

/-! # Glued Picard Difference Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GluedPicardDifferenceIsogeny.DualOpenGluing

noncomputable section

/-! The local original translation isogenies give an actual global
finite etale inducing isogeny. Descent of the original difference line
then supplies the original normalized dual abelian data. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ}
  (A : Abelian.Schemes.AbelianScheme g S) (U : S.OpenCover.{0})
  (D : ∀ j, Dual.Data.DualAbelianData (A.pullback (U.f j)))
  (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)

/-- Original local inducing isogenies and their actual represented
classes. The affine ample-translation quotients provide these data. -/
structure DifferenceIsogenyCharts where
  isogeny : ∀ j, Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (U.f j)) (D j).abelian
  etale : ∀ j, Etale (isogeny j).hom.left
  classifies : ∀ j, (D j).representable.homEquiv (isogeny j).hom =
    RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (A.pullback (U.f j))
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle (A.pullback (U.f j))
        (L.pullback (pullback.fst A.scheme.hom (U.f j))))
      (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous (A.pullback (U.f j))
        (P.baseChange (U.f j)) (L.pullback (pullback.fst A.scheme.hom (U.f j))))
      (𝟙 (A.pullback (U.f j)).scheme)

variable (C : DifferenceIsogenyCharts A U D P L)

include C in
theorem differenceMorphism_property
    (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    (hQ : ∀ j, Q (C.isogeny j).hom.left) :
    Q (GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism A U D P L).left := by
  apply HilbertConstruction.Over.MorphismPropertyOpenDescent.overMorphism_property_of_openCover (GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism A U D P L) U Q
  intro j
  let e : Arrow.mk (C.isogeny j).hom.left ≅
      Arrow.mk ((Over.pullback (U.f j)).map (GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism A U D P L)).left :=
    Arrow.isoMk (Iso.refl _) ((Over.forget (U.X j)).mapIso (Dual.OpenGluingScheme.DualOpenGluing.chartIso A U D j)) (by
      change 𝟙 _ ≫ ((Over.pullback (U.f j)).map (GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism A U D P L)).left =
        (C.isogeny j).hom.left ≫ (Dual.OpenGluingScheme.DualOpenGluing.chartIso A U D j).hom.left
      exact (Category.id_comp _).trans
        (congrArg Over.Hom.left
          (GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism_chart A U D P L j (C.isogeny j).hom (C.classifies j))))
  exact (Q.arrow_mk_iso_iff e).mp (hQ j)

include C in
theorem differenceMorphism_finite : IsFinite (GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism A U D P L).left := by
  let : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{0}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop
  exact differenceMorphism_property A U D P L C (@IsFinite) (fun j => (C.isogeny j).finite)

include C in
theorem differenceMorphism_etale : Etale (GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism A U D P L).left := by
  let : IsZariskiLocalAtTarget (@Etale : MorphismProperty Scheme.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale) (Q := RingHom.Etale)
  exact differenceMorphism_property A U D P L C (@Etale) C.etale

include C in
theorem differenceMorphism_surjective : Surjective (GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism A U D P L).left :=
  differenceMorphism_property A U D P L C (@Surjective) (fun j => (C.isogeny j).surjective)

def differenceIsogeny : Abelian.Schemes.AbelianScheme.Isogeny A (Dual.OpenGluingScheme.DualOpenGluing.abelian A U D) where
  hom := GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism A U D P L
  preservesGroup := GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism_isMonHom A U D P L
  finite := differenceMorphism_finite A U D P L C
  flat := by
    let : Etale (GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism A U D P L).left := differenceMorphism_etale A U D P L C
    infer_instance
  surjective := differenceMorphism_surjective A U D P L C

instance differenceIsogeny_etale : Etale (differenceIsogeny A U D P L C).hom.left :=
  differenceMorphism_etale A U D P L C

def dualData : Dual.Data.DualAbelianData A :=
  RepresentedDifferenceDualData.RepresentedDifferenceDual.dualData A (Dual.OpenGluingScheme.DualOpenGluing.abelian A U D) L (Dual.OpenGluingScheme.DualOpenGluing.representable A U D)
    (differenceIsogeny A U D P L C) (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous A P L)
    (GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism_class A U D P L)

def inducingIsogeny : Abelian.Schemes.AbelianScheme.Isogeny A (dualData A U D P L C).abelian :=
  differenceIsogeny A U D P L C

instance inducingIsogeny_etale : Etale (inducingIsogeny A U D P L C).hom.left :=
  differenceMorphism_etale A U D P L C

def poincareRecovery :
    (((dualData A U D P L C).poincare).pullback
      ((inducingIsogeny A U D P L C).hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf :=
  RepresentedDifferenceDualData.RepresentedDifferenceDual.recovery A (Dual.OpenGluingScheme.DualOpenGluing.abelian A U D) L (Dual.OpenGluingScheme.DualOpenGluing.representable A U D)
    (differenceIsogeny A U D P L C) (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous A P L)
    (GluedPicardDifferenceMap.DualOpenGluing.differenceMorphism_class A U D P L)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GluedPicardDifferenceIsogeny.DualOpenGluing
