import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferenceFieldSpecialization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferenceTwistEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.DifferenceNonrealization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CartesianVanishingReflection

/-! # Difference Twist Field Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferenceTwistFieldVanishing

noncomputable section

/-! If an ample difference map misses a homogeneous line, every field
fiber of its twisted difference family is a nontrivial homogeneous
line. Proper flat cohomology then vanishes on the entire square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

local instance differenceFiberClassCommGroup (X : Scheme) : CommGroup (Line.Bundles.LineBundle.IsoClass X) :=
  Line.Bundles.LineBundle.isoClassCommGroup X

variable {k K : Type} [Field k] [Field K] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (c : Spec (.of K) ⟶ Spec (.of k))
    (x : (Over.map c).obj (Over.mk (𝟙 (Spec (.of K)))) ⟶ A.scheme)

theorem differenceTwistedLine_field_class (L M : Line.Bundles.LineBundle A.scheme.left) :
    Line.Bundles.LineBundle.classOf ((DifferenceTwistEuler.differenceTwistedLine A L M).pullback
      (DifferenceFieldSpecialization.differenceFieldSpecializationMap A c x)) =
      Line.Bundles.LineBundle.classOf ((DifferencePointBundles.differencePointBundle (A.pullback c)
        (L.pullback (pullback.fst A.scheme.hom c))
        (DifferenceFieldSpecialization.differenceFieldSpecializationPoint A c x)).tensor
          (M.pullback (pullback.fst A.scheme.hom c))) := by
  let t := DifferenceFieldSpecialization.differenceFieldSpecializationMap A c x
  let p : (A.pullback c).scheme.left ⟶ A.scheme.left := pullback.fst A.scheme.hom c
  let a := DifferenceFieldSpecialization.differenceFieldSpecializationPoint A c x
  have hd : Line.Bundles.LineBundle.pullbackClass t (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)) =
      Line.Bundles.LineBundle.classOf (DifferencePointBundles.differencePointBundle (A.pullback c) (L.pullback p) a) :=
    DifferenceFieldSpecialization.differenceFieldSpecialization_class A L c x
  have hscalar : Line.Bundles.LineBundle.pullbackClass x.left (Line.Bundles.LineBundle.classOf L) = 1 :=
    Quotient.sound (RepresentationTheory.Theta.Geometric.LineBundleFieldTriviality.lineBundle_over_field_trivial K (L.pullback x.left))
  have htF : t ≫ (fst A.scheme A.scheme).left = (A.pullback c).scheme.hom ≫ x.left :=
    DifferenceFieldSpecialization.differenceFieldSpecializationMap_fst A c x
  have htS : t ≫ (snd A.scheme A.scheme).left = p :=
    DifferenceFieldSpecialization.differenceFieldSpecializationMap_snd A c x
  have hf : Line.Bundles.LineBundle.pullbackClass t
      (Line.Bundles.LineBundle.pullbackClass (fst A.scheme A.scheme).left (Line.Bundles.LineBundle.classOf L)) = 1 := by
    rw [← Line.Bundles.LineBundle.pullbackClass_comp, htF,
      Line.Bundles.LineBundle.pullbackClass_comp, hscalar]
    exact (Line.Bundles.LineBundle.pullbackClassMonoidHom (A.pullback c).scheme.hom).map_one
  have hs : Line.Bundles.LineBundle.pullbackClass t
      (Line.Bundles.LineBundle.pullbackClass (snd A.scheme A.scheme).left (Line.Bundles.LineBundle.classOf M)) =
      Line.Bundles.LineBundle.pullbackClass p (Line.Bundles.LineBundle.classOf M) := by
    rw [← Line.Bundles.LineBundle.pullbackClass_comp, htS]
  change Line.Bundles.LineBundle.pullbackClass t
    ((Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) *
      Line.Bundles.LineBundle.pullbackClass (fst A.scheme A.scheme).left (Line.Bundles.LineBundle.classOf L)) *
        Line.Bundles.LineBundle.pullbackClass (snd A.scheme A.scheme).left (Line.Bundles.LineBundle.classOf M)) = _
  rw [Line.Bundles.LineBundle.pullbackClass_mul, Line.Bundles.LineBundle.pullbackClass_mul, hd, hf, hs, mul_one]
  rfl

theorem reciprocalFrameBundle_pullback_class {X Y : Scheme} (f : X ⟶ Y)
    (N : Line.Bundles.LineBundle Y) :
    Line.Bundles.LineBundle.classOf (N.reciprocalFrameBundle.pullback f) =
      Line.Bundles.LineBundle.classOf ((N.pullback f).reciprocalFrameBundle) := by
  change Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.classOf N.reciprocalFrameBundle) = _
  rw [Line.Bundles.LineBundle.classOf_reciprocalFrameBundle, Line.Bundles.LineBundle.classOf_reciprocalFrameBundle]
  exact (Line.Bundles.LineBundle.pullbackClassMonoidHom f).map_inv _

theorem differenceTwistedLine_field_ratio_class (L N : Line.Bundles.LineBundle A.scheme.left) :
    Line.Bundles.LineBundle.classOf ((DifferenceTwistEuler.differenceTwistedLine A L N.reciprocalFrameBundle).pullback
      (DifferenceFieldSpecialization.differenceFieldSpecializationMap A c x)) =
      Line.Bundles.LineBundle.classOf (DifferencePointBundles.differencePointRatio (A.pullback c)
        (L.pullback (pullback.fst A.scheme.hom c))
        (N.pullback (pullback.fst A.scheme.hom c))
        (DifferenceFieldSpecialization.differenceFieldSpecializationPoint A c x)) := by
  let p : (A.pullback c).scheme.left ⟶ A.scheme.left := pullback.fst A.scheme.hom c
  let Q := DifferencePointBundles.differencePointBundle (A.pullback c) (L.pullback p)
    (DifferenceFieldSpecialization.differenceFieldSpecializationPoint A c x)
  calc
    _ = Line.Bundles.LineBundle.classOf Q * Line.Bundles.LineBundle.classOf (N.reciprocalFrameBundle.pullback p) :=
      differenceTwistedLine_field_class A c x L N.reciprocalFrameBundle
    _ = Line.Bundles.LineBundle.classOf Q * Line.Bundles.LineBundle.classOf ((N.pullback p).reciprocalFrameBundle) :=
      congrArg (fun q : Line.Bundles.LineBundle.IsoClass (A.pullback c).scheme.left => Line.Bundles.LineBundle.classOf Q * q)
        (reciprocalFrameBundle_pullback_class p N)
    _ = _ := rfl

theorem differenceTwistedLine_field_cohomology_vanish
    [IsAlgClosed k] (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L N : Line.Bundles.LineBundle A.scheme.left)
    (hN : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf N))
    (hne : ¬ Picard.ThetaConstruction.DifferenceParameterTransport.Geometric.HasDifferenceParameter A L N) (m q : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
      ((DifferenceTwistEuler.differenceTwistedLine A (L.tensorPower m) N.reciprocalFrameBundle).pullback
        (DifferenceFieldSpecialization.differenceFieldSpecializationMap A c x)).sheaf q) := by
  have h := HilbertConstruction.Field.DifferenceNonrealization.differencePointRatio_baseChanged_cohomology_vanish A P L N hN hne c m
    (DifferenceFieldSpecialization.differenceFieldSpecializationPoint A c x) q
  obtain ⟨e⟩ := Quotient.exact (differenceTwistedLine_field_ratio_class A c x (L.tensorPower m) N)
  let d := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (A.pullback c).scheme.left q).mapIso e
  exact ⟨fun v w => (AddCommGrpCat.mono_iff_injective d.hom).mp inferInstance
    (h.elim _ _)⟩

theorem differenceTwistedLine_cohomology_vanish_of_no_parameter
    [IsAlgClosed k] (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L N : Line.Bundles.LineBundle A.scheme.left)
    (hN : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf N))
    (hne : ¬ Picard.ThetaConstruction.DifferenceParameterTransport.Geometric.HasDifferenceParameter A L N) (m q : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
      (DifferenceTwistEuler.differenceTwistedLine A (L.tensorPower m) N.reciprocalFrameBundle).sheaf q) := by
  have : A.scheme.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.scheme.hom]
    infer_instance
  have : IsLocallyNoetherian A.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
  let f := (fst A.scheme A.scheme).left
  have : IsProper f := inferInstanceAs (IsProper (pullback.fst A.scheme.hom A.scheme.hom))
  have : Flat f := inferInstanceAs (Flat (pullback.fst A.scheme.hom A.scheme.hom))
  let F := DifferenceTwistEuler.differenceTwistedLine A (L.tensorPower m) N.reciprocalFrameBundle
  apply ProperFlat.FiberwiseVanishing.properFlat_cohomology_vanish_of_field_fibers f F
  intro K _ s r
  let c' := s ≫ A.scheme.hom
  let x' : (Over.map c').obj (Over.mk (𝟙 (Spec (.of K)))) ⟶ A.scheme :=
    Over.homMk s (by simp [c'])
  have h := differenceTwistedLine_field_cohomology_vanish A c' x' P L N hN hne m r
  exact (HilbertConstruction.Field.CartesianVanishingReflection.lineBundle_fieldCartesian_cohomology_vanish_iff f F s
    (DifferenceFieldSpecialization.differenceFieldSpecialization_isPullback A c' x') r).mpr h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferenceTwistFieldVanishing
