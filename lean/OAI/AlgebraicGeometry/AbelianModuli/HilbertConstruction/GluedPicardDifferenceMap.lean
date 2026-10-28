import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.OpenGluingScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.DifferenceHomomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.PoincareClasses
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PicardInclusionFaithfulness
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceBaseChangeValues
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.HomogeneousBaseChangeForgetting
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MapFromPointProducts

/-! # Glued Picard Difference Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The global translation morphism into the glued Picard representative
and its native recovery from each local original inducing morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ}

theorem GluedPicardDifferenceMap.relativeDifferenceHomogeneousClass_baseChange
    (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left)
    (hHom : A.IsHomogeneousPicardClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)))
    {V : Scheme.{0}} (f : V ⟶ S)
    (hHom' : (A.pullback f).IsHomogeneousPicardClass (A.pullback f).scheme
      (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle (A.pullback f)
        (L.pullback (pullback.fst A.scheme.hom f)))))
    (T : Over V) (a : T ⟶ (A.pullback f).scheme) :
    A.homogeneousPicardBaseChangeEquiv f T
        (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (A.pullback f)
          (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle (A.pullback f) (L.pullback (pullback.fst A.scheme.hom f)))
            hHom' a) =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom
        (A.baseChangePointsEquiv f T a) := by
  let q := RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousClass (A.pullback f)
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle (A.pullback f) (L.pullback (pullback.fst A.scheme.hom f))) hHom' a
  apply A.homogeneousPicardSectionInclusion_injective ((Over.map f).obj T)
  change A.homogeneousPicardSheafInclusion.hom.app (.op ((Over.map f).obj T))
      (A.homogeneousPicardBaseChangeEquiv f T
        ((toSheafify (Scheme.fppfTopology.over V) (A.pullback f).homogeneousPicardPresheaf).app (.op T) q)) = _
  calc
    _ = (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op ((Over.map f).obj T))
        ((A.homogeneousPicardPresheafBaseChangeIso f).hom.app (.op T) q).val :=
      (congrArg (A.homogeneousPicardSheafInclusion.hom.app (.op ((Over.map f).obj T)))
        (A.toHomogeneousPicard_baseChange_apply f T q)).trans
          (Picard.ThetaConstruction.HomogeneousBaseChangeForgetting.Geometric.homogeneousForget_toSheafify A ((Over.map f).obj T) _)
    _ = Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f T
        ((Picard.PicardSheaf.toRelativePicard (A.pullback f).scheme).app (.op T) q.val) :=
      (Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme f T q.val).symm
    _ = (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (A.baseChangePointsEquiv f T a) :=
      Picard.ThetaConstruction.DifferenceBaseChangeValues.Geometric.relativeDifference_value_baseChange A L f T a
    _ = _ := (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom
      (A.baseChangePointsEquiv f T a)).symm

theorem Dual.Data.DualAbelianData.differenceMap_class_of_recovery
    {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A) (L : Line.Bundles.LineBundle A.scheme.left)
    (hHom : A.IsHomogeneousPicardClass A.scheme (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)))
    (m : A.scheme ⟶ D.abelian.scheme)
    (e : (D.poincare.pullback (m ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf) :
    D.representable.homEquiv m =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom (𝟙 A.scheme) := by
  have hc : A.homogeneousPicardPresheaf.map m.op D.poincareClass =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) hHom (𝟙 A.scheme) := by
    apply Subtype.ext
    change Line.Bundles.LineBundle.pullbackClass (m ⊗ₘ 𝟙 A.scheme).left (Line.Bundles.LineBundle.classOf D.poincare) =
      Line.Bundles.LineBundle.pullbackClass ((𝟙 A.scheme) ⊗ₘ 𝟙 A.scheme).left
        (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L))
    rw [id_tensorHom_id]
    change Line.Bundles.LineBundle.pullbackClass (m ⊗ₘ 𝟙 A.scheme).left (Line.Bundles.LineBundle.classOf D.poincare) =
      Line.Bundles.LineBundle.pullbackClass (𝟙 (A.scheme ⊗ A.scheme).left)
        (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L))
    have he : Line.Bundles.LineBundle.pullbackClass (m ⊗ₘ 𝟙 A.scheme).left (Line.Bundles.LineBundle.classOf D.poincare) =
        Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L) := Quotient.sound ⟨e⟩
    exact he.trans (Line.Bundles.LineBundle.pullbackClass_id _).symm
  exact (D.pointClass_eq_poincare m).trans
    (congrArg (A.toHomogeneousPicard.app (.op A.scheme)) hc)

namespace GluedPicardDifferenceMap.DualOpenGluing

variable [IsLocallyNoetherian S] (A : Abelian.Schemes.AbelianScheme g S) (U : S.OpenCover.{0})
  (D : ∀ j, Dual.Data.DualAbelianData (A.pullback (U.f j)))
  (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (L : Line.Bundles.LineBundle A.scheme.left)

def differenceMorphism : A.scheme ⟶ (Dual.OpenGluingScheme.DualOpenGluing.abelian A U D).scheme :=
  (Dual.OpenGluingScheme.DualOpenGluing.representable A U D).homEquiv.symm
    (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)
      (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous A P L) (𝟙 A.scheme))

theorem differenceMorphism_class :
    (Dual.OpenGluingScheme.DualOpenGluing.representable A U D).homEquiv (differenceMorphism A U D P L) =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)
        (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous A P L) (𝟙 A.scheme) :=
  (Dual.OpenGluingScheme.DualOpenGluing.representable A U D).homEquiv.apply_symm_apply _

theorem differenceMorphism_points {T : Over S} (a : T ⟶ A.scheme) :
    (Dual.OpenGluingScheme.DualOpenGluing.representable A U D).homEquiv (a ≫ differenceMorphism A U D P L) =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)
        (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous A P L) a := by
  let dm : A.scheme ⟶ Dual.OpenGluingScheme.DualOpenGluing.scheme A U D := differenceMorphism A U D P L
  exact ((Dual.OpenGluingScheme.DualOpenGluing.representable A U D).homEquiv_comp a dm).trans
    ((congrArg (A.homogeneousPicardSheaf.obj.map a.op) (differenceMorphism_class A U D P L)).trans
      ((RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_naturality A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)
        (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous A P L) (𝟙 A.scheme) a).trans
        (congrArg (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)
          (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous A P L)) (Category.comp_id a))))

theorem differenceMorphism_isMonHom : IsMonHom (differenceMorphism A U D P L) := by
  let : GrpObj (Dual.OpenGluingScheme.DualOpenGluing.scheme A U D) := Dual.OpenGluingScheme.DualOpenGluing.group A U D
  apply Picard.PoincareBundle.MapFromPointProducts.Group.isMonHom
  intro T a b
  let dm : A.scheme ⟶ Dual.OpenGluingScheme.DualOpenGluing.scheme A U D := differenceMorphism A U D P L
  apply (Dual.OpenGluingScheme.DualOpenGluing.groupHomEquiv A U D T).injective
  have hmul : (Dual.OpenGluingScheme.DualOpenGluing.representable A U D).homEquiv ((a ≫ dm) * (b ≫ dm)) =
      (Dual.OpenGluingScheme.DualOpenGluing.representable A U D).homEquiv (a ≫ dm) * (Dual.OpenGluingScheme.DualOpenGluing.representable A U D).homEquiv (b ≫ dm) :=
    (Dual.OpenGluingScheme.DualOpenGluing.groupHomEquiv A U D T).map_mul (a ≫ dm) (b ≫ dm)
  exact (differenceMorphism_points A U D P L (a * b)).trans
    ((LocallyNoetherian.DifferenceHomomorphism.Theta.Geometric.locallyNoetherian_parameterDifferenceHomogeneousClass_mul A P L _ a b).trans
      ((congrArg₂ (fun x y => x * y) (differenceMorphism_points A U D P L a)
        (differenceMorphism_points A U D P L b)).symm.trans hmul.symm))

omit [IsLocallyNoetherian S] in
theorem chartIso_points (j : U.I₀) {T : Over (U.X j)}
    (a : T ⟶ (D j).abelian.scheme) :
    (Open.CoverRepresentability.restrictSchemeRepresentable (Dual.OpenGluingScheme.DualOpenGluing.representable A U D) (U.f j)).homEquiv
        (a ≫ (Dual.OpenGluingScheme.DualOpenGluing.chartIso A U D j).hom) =
      (Dual.OpenGluingScheme.DualOpenGluing.localRepresentable A U D j).homEquiv a := by
  let r := Open.CoverRepresentability.restrictSchemeRepresentable (Dual.OpenGluingScheme.DualOpenGluing.representable A U D) (U.f j)
  have hi : r.homEquiv (Dual.OpenGluingScheme.DualOpenGluing.chartIso A U D j).hom =
      (Dual.OpenGluingScheme.DualOpenGluing.localRepresentable A U D j).homEquiv (𝟙 (D j).abelian.scheme) :=
    Open.CoverRepresentability.OpenCoverRepresentability.chartPullbackIso_class A.homogeneousPicardSheaf.obj U
      (fun i => (D i).abelian.scheme) (Dual.OpenGluingScheme.DualOpenGluing.localRepresentable A U D)
      A.homogeneousPicard_isSheaf_zariski j
  exact (r.homEquiv_comp a (Dual.OpenGluingScheme.DualOpenGluing.chartIso A U D j).hom).trans
    ((congrArg (((Over.map (U.f j)).op ⋙ A.homogeneousPicardSheaf.obj).map a.op) hi).trans
      ((Dual.OpenGluingScheme.DualOpenGluing.localRepresentable A U D j).homEquiv_eq a).symm)

theorem differenceMorphism_chart (j : U.I₀)
    (m : (A.pullback (U.f j)).scheme ⟶ (D j).abelian.scheme)
    (hm : (D j).representable.homEquiv m =
      RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (A.pullback (U.f j))
        (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle (A.pullback (U.f j)) (L.pullback (pullback.fst A.scheme.hom (U.f j))))
        (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous (A.pullback (U.f j)) (P.baseChange (U.f j))
          (L.pullback (pullback.fst A.scheme.hom (U.f j))))
        (𝟙 (A.pullback (U.f j)).scheme)) :
    (Over.pullback (U.f j)).map (differenceMorphism A U D P L) = m ≫ (Dual.OpenGluingScheme.DualOpenGluing.chartIso A U D j).hom := by
  let f := U.f j
  let T := (A.pullback f).scheme
  let x := A.baseChangePointsEquiv f T (𝟙 T)
  let r := Open.CoverRepresentability.restrictSchemeRepresentable (Dual.OpenGluingScheme.DualOpenGluing.representable A U D) f
  let dm : A.scheme ⟶ Dual.OpenGluingScheme.DualOpenGluing.scheme A U D := differenceMorphism A U D P L
  have hx : ((Over.mapPullbackAdj f).homEquiv T (Dual.OpenGluingScheme.DualOpenGluing.scheme A U D)).symm
        ((Over.pullback f).map dm) = x ≫ dm := by
    apply Over.OverMorphism.ext
    change ((Over.pullback f).map dm).left ≫
      pullback.fst (Dual.OpenGluingScheme.DualOpenGluing.scheme A U D).hom f =
        ((𝟙 T.left) ≫ pullback.fst A.scheme.hom f) ≫ dm.left
    exact (Pullback.Comparisons.overPullback_map_left_fst dm f).trans
      (congrArg (fun a => a ≫ dm.left) (Category.id_comp (pullback.fst A.scheme.hom f)).symm)
  apply r.homEquiv.injective
  calc
    _ = (Dual.OpenGluingScheme.DualOpenGluing.representable A U D).homEquiv (x ≫ differenceMorphism A U D P L) :=
      congrArg (Dual.OpenGluingScheme.DualOpenGluing.representable A U D).homEquiv hx
    _ = RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)
        (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous A P L) x := differenceMorphism_points A U D P L x
    _ = A.homogeneousPicardBaseChangeEquiv f T
        (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (A.pullback f)
          (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle (A.pullback f) (L.pullback (pullback.fst A.scheme.hom f)))
          (LocallyNoetherian.RelativeCube.Theta.Geometric.locallyNoetherian_difference_homogeneous (A.pullback f) (P.baseChange f)
            (L.pullback (pullback.fst A.scheme.hom f))) (𝟙 T)) :=
      (relativeDifferenceHomogeneousClass_baseChange A L _ f _ T (𝟙 T)).symm
    _ = A.homogeneousPicardBaseChangeEquiv f T ((D j).representable.homEquiv m) :=
      congrArg (A.homogeneousPicardBaseChangeEquiv f T) hm.symm
    _ = (Dual.OpenGluingScheme.DualOpenGluing.localRepresentable A U D j).homEquiv m := rfl
    _ = _ := (chartIso_points A U D j m).symm

end GluedPicardDifferenceMap.DualOpenGluing

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
