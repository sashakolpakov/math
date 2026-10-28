import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceDifferenceFamilyMaps

/-! # Difference Parameter Transport -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceParameterTransport.Geometric

noncomputable section

/-! An actual difference-line parameter remains a parameter under
base change and under an original group isomorphism with recovered
line classes. The equalities remain in the original Picard sheaf. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {S S' : Scheme.{0}} {g h : ℕ}

def HasDifferenceParameter (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) : Prop :=
  ∃ a : Over.mk (𝟙 S) ⟶ A.scheme,
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
      ReferenceLineValues.Geometric.originalLineValue A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N) (Over.mk (𝟙 S))

theorem HasDifferenceParameter.baseChange (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (L N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (b : S' ⟶ S) (h : HasDifferenceParameter A L N) :
    HasDifferenceParameter (A.pullback b) (L.pullback (pullback.fst A.scheme.hom b))
      (N.pullback (pullback.fst A.scheme.hom b)) := by
  obtain ⟨a, ha⟩ := h
  let U := Over.mk (𝟙 S)
  let V := Over.mk (𝟙 S')
  let W := (Over.map b).obj V
  let t : W ⟶ U := Over.homMk b (by
    change b ≫ 𝟙 S = 𝟙 S' ≫ b
    simp only [Category.comp_id, Category.id_comp])
  let a' := (A.baseChangePointsEquiv b V).symm (t ≫ a)
  have hs : A.baseChangePointsEquiv b V a' = t ≫ a :=
    (A.baseChangePointsEquiv b V).apply_symm_apply _
  have ht : (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (t ≫ a) =
      ReferenceLineValues.Geometric.originalLineValue A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N) W :=
    (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass_naturality (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).bundle a t).symm.trans
      ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map t.op) ha).trans
        (ReferenceLineValues.Geometric.originalLineValue_naturality A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N) t))
  refine ⟨a', ?_⟩
  apply (AbelianModuli.HilbertConstruction.Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme b V).injective
  exact (DifferenceBaseChangeValues.Geometric.relativeDifference_value_baseChange A L b V a').trans
    ((congrArg (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue hs).trans
      (ht.trans (ReferenceLineValues.Geometric.originalLineValue_baseChange A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N) b V).symm))

theorem HasDifferenceParameter.of_groupIso (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (L N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (LB NB : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.scheme.left)
    (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.hom.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf LB) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
    (hN : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.hom.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf NB) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N)
    (h : HasDifferenceParameter B LB NB) : HasDifferenceParameter A L N := by
  obtain ⟨b, hb⟩ := h
  let U := Over.mk (𝟙 S)
  let a : U ⟶ A.scheme := b ≫ e.inv
  have ha : a ≫ e.hom = b := by simp [a]
  have hf := ReferenceDifferenceFamilyMaps.Geometric.relativeDifference_value_familyMap A B e.hom LB a
  rw [ha] at hf
  have ht : (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A (LB.pullback e.hom.left)).relativeValue a =
      ReferenceLineValues.Geometric.originalLineValue A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.hom.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf NB)) U :=
    hf.symm.trans ((congrArg ((AbelianModuli.HilbertConstruction.Picard.FamilySheafMaps.relativePicardSheafMap e.hom).hom.app (.op U)) hb).trans
      (ReferenceLineValues.Geometric.originalLineValue_familyMap A B e.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf NB) U))
  exact ⟨a, (ReferenceDifferenceFamilyMaps.Geometric.relativeDifference_value_class_congr A (LB.pullback e.hom.left) L hL a).symm.trans
    (ht.trans (congrArg (fun q => ReferenceLineValues.Geometric.originalLineValue A q U) hN))⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceParameterTransport.Geometric
