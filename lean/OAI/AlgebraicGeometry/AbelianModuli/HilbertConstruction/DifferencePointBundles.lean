import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.RelativeCube
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceLineValues
import OAI.AlgebraicGeometry.Picard.Homomorphisms.HomogeneousGroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousLinePowers

/-! # Difference Point Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferencePointBundles

noncomputable section

/-! The line at a rational point of the normalized difference family is
homogeneous. Its ratio with a prescribed homogeneous line is nontrivial
unless that point realizes the prescribed relative Picard value. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

local instance differencePointPicardGroup (X : Scheme) : CommGroup (Line.Bundles.LineBundle.IsoClass X) :=
  Picard.Homomorphisms.SchemeGroup.Construction.lineBundleClassCommGroup X

variable {k : Type} [Field k] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g (Spec (.of k)))

def differencePointMap (a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme) :
    A.scheme ⟶ A.scheme ⊗ A.scheme :=
  lift (toUnit A.scheme ≫ a) (𝟙 A.scheme)

def differencePointBundle (L : Line.Bundles.LineBundle A.scheme.left)
    (a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme) : Line.Bundles.LineBundle A.scheme.left :=
  (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).pullback (differencePointMap A a).left

theorem differencePointMap_family (a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme) :
    snd (Over.mk (𝟙 (Spec (.of k)))) A.scheme ≫ differencePointMap A a =
      a ⊗ₘ 𝟙 A.scheme := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, differencePointMap, lift_fst, tensorHom_fst]
    have h : snd (Over.mk (𝟙 (Spec (.of k)))) A.scheme ≫ toUnit A.scheme =
        fst (Over.mk (𝟙 (Spec (.of k)))) A.scheme := Subsingleton.elim _ _
    rw [← Category.assoc, h]
  · simp [differencePointMap]

theorem differencePointBundle_family (L : Line.Bundles.LineBundle A.scheme.left)
    (a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme) :
    ReferenceFamily.HomogeneousLinePowers.constantLineFamily A (Over.mk (𝟙 (Spec (.of k))))
        (Line.Bundles.LineBundle.classOf (differencePointBundle A L a)) =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) a := by
  change Line.Bundles.LineBundle.pullbackClass (snd (Over.mk (𝟙 (Spec (.of k)))) A.scheme).left
      (Line.Bundles.LineBundle.pullbackClass (differencePointMap A a).left
        (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L))) = _
  rw [← Line.Bundles.LineBundle.pullbackClass_comp]
  exact congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)))
    (congrArg Over.Hom.left (differencePointMap_family A a))

theorem differencePointBundle_homogeneous (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (L : Line.Bundles.LineBundle A.scheme.left) (a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme) :
    ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf (differencePointBundle A L a)) := by
  change A.IsHomogeneousPicardClass (Over.mk (𝟙 (Spec (.of k))))
    (ReferenceFamily.HomogeneousLinePowers.constantLineFamily A (Over.mk (𝟙 (Spec (.of k))))
      (Line.Bundles.LineBundle.classOf (differencePointBundle A L a)))
  rw [differencePointBundle_family]
  exact (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous A P L).pullback A a

theorem differencePointBundle_value (L : Line.Bundles.LineBundle A.scheme.left)
    (a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
      Picard.ThetaConstruction.ReferenceLineValues.Geometric.originalLineValue A (Line.Bundles.LineBundle.classOf (differencePointBundle A L a))
        (Over.mk (𝟙 (Spec (.of k)))) :=
  congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (Over.mk (𝟙 (Spec (.of k))))))
    (differencePointBundle_family A L a).symm

theorem homogeneousLine_tensor (L M : Line.Bundles.LineBundle A.scheme.left)
    (hL : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf L))
    (hM : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf M)) :
    ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf (L.tensor M)) := by
  let U := Over.mk (𝟙 (Spec (.of k)))
  let p := RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd U A.scheme).left
  have he : p (Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf M) =
      p (Line.Bundles.LineBundle.classOf L) * p (Line.Bundles.LineBundle.classOf M) := p.map_mul _ _
  exact (congrArg (A.IsHomogeneousPicardClass U) he).mpr
    (Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardClass_mul A hL hM)

theorem reciprocalFrameBundle_class_as_picard_inverse {X : Scheme} (L : Line.Bundles.LineBundle X) :
    Line.Bundles.LineBundle.classOf L.reciprocalFrameBundle = (Line.Bundles.LineBundle.classOf L)⁻¹ :=
  eq_inv_of_mul_eq_one_left (Quotient.sound ⟨L.reciprocalFrameTensorIso⟩)

theorem homogeneousLine_reciprocal (L : Line.Bundles.LineBundle A.scheme.left)
    (hL : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf L)) :
    ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf L.reciprocalFrameBundle) := by
  let U := Over.mk (𝟙 (Spec (.of k)))
  change A.IsHomogeneousPicardClass U
    (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd U A.scheme).left (Line.Bundles.LineBundle.classOf L.reciprocalFrameBundle))
  rw [reciprocalFrameBundle_class_as_picard_inverse, map_inv]
  exact Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardClass_inv A hL

def differencePointRatio (L N : Line.Bundles.LineBundle A.scheme.left)
    (a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme) : Line.Bundles.LineBundle A.scheme.left :=
  (differencePointBundle A L a).tensor N.reciprocalFrameBundle

theorem differencePointRatio_homogeneous (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (L N : Line.Bundles.LineBundle A.scheme.left) (a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)
    (hN : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf N)) :
    ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf (differencePointRatio A L N a)) :=
  homogeneousLine_tensor A _ _ (differencePointBundle_homogeneous A P L a)
    (homogeneousLine_reciprocal A N hN)

theorem differencePointRatio_nontrivial (L N : Line.Bundles.LineBundle A.scheme.left)
    (a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme)
    (hne : (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a ≠
      Picard.ThetaConstruction.ReferenceLineValues.Geometric.originalLineValue A (Line.Bundles.LineBundle.classOf N) (Over.mk (𝟙 (Spec (.of k))))) :
    ¬ Nonempty ((differencePointRatio A L N a).sheaf ≅ Line.Bundles.structureModule A.scheme.left) := by
  intro ht
  have hc : Line.Bundles.LineBundle.classOf (differencePointBundle A L a) *
      (Line.Bundles.LineBundle.classOf N)⁻¹ = 1 := by
    have h : Line.Bundles.LineBundle.classOf (differencePointRatio A L N a) =
        Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.trivial A.scheme.left) := Quotient.sound ht
    change Line.Bundles.LineBundle.classOf (differencePointBundle A L a) *
      Line.Bundles.LineBundle.classOf N.reciprocalFrameBundle = 1 at h
    rwa [reciprocalFrameBundle_class_as_picard_inverse] at h
  have he := mul_inv_eq_one.mp hc
  exact hne ((differencePointBundle_value A L a).trans
    (congrArg (fun q => Picard.ThetaConstruction.ReferenceLineValues.Geometric.originalLineValue A q (Over.mk (𝟙 (Spec (.of k))))) he))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferencePointBundles
