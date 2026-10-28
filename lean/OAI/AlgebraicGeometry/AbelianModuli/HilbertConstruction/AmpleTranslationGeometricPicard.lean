import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmpleDifferenceSurjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TranslationPicardInjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.HomogeneousBaseChangeForgetting
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClosedSheafification

/-! # Ample Translation Geometric Picard -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Translation by an actual ample line realizes every section of
the original homogeneous Picard sheaf at an arbitrary geometric
field point in every characteristic. The underlying line is constructed. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

namespace AmpleTranslationGeometricPicard.Theta.Geometric

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L : Line.Bundles.LineBundle A.scheme.left)

theorem algebraic_ampleDifference_surjective (hL : L.IsAmple)
    (q : A.homogeneousPicardSheaf.obj.obj (.op (Over.mk (𝟙 (Spec (.of k)))))) :
    ∃ a : Over.mk (𝟙 (Spec (.of k))) ⟶ A.scheme,
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
        A.homogeneousPicardSheafInclusion.hom.app (.op (Over.mk (𝟙 (Spec (.of k))))) q := by
  let U := Over.mk (𝟙 (Spec (.of k)))
  obtain ⟨r, hr⟩ := (ReferenceFamily.ClosedSheafification.fppf_toSheafify_bijective_at_algClosed (𝟙 (Spec (.of k)))
    A.homogeneousPicardPresheaf).surjective q
  let r₀ : {z : Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left // A.IsHomogeneousPicardClass U z} := r
  let t : A.scheme ⟶ U := Over.mkIdTerminal.from A.scheme
  let j : A.scheme ⟶ U ⊗ A.scheme := lift t (𝟙 A.scheme)
  have hj : snd U A.scheme ≫ j = 𝟙 (U ⊗ A.scheme) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [j, Category.assoc, lift_fst, Category.id_comp]
      exact Over.mkIdTerminal.hom_ext _ _
    · simp [j]
  let N : Line.Bundles.LineBundle A.scheme.left := r₀.val.out.pullback j.left
  have hc : Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left (Line.Bundles.LineBundle.classOf N) = r₀.val := by
    have ho : Line.Bundles.LineBundle.classOf r₀.val.out = r₀.val := Quotient.out_eq _
    have hj' : (snd U A.scheme).left ≫ j.left = 𝟙 (U ⊗ A.scheme).left :=
      congrArg Over.Hom.left hj
    have hcomp : Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left
        (Line.Bundles.LineBundle.pullbackClass j.left r₀.val) = r₀.val :=
      (Line.Bundles.LineBundle.pullbackClass_comp (snd U A.scheme).left j.left r₀.val).symm.trans
        ((congrArg (fun f : (U ⊗ A.scheme).left ⟶ (U ⊗ A.scheme).left =>
          Line.Bundles.LineBundle.pullbackClass f r₀.val) hj').trans (Line.Bundles.LineBundle.pullbackClass_id r₀.val))
    exact (congrArg (fun z : Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left =>
      Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left (Line.Bundles.LineBundle.pullbackClass j.left z)) ho).trans hcomp
  have hN : ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (Line.Bundles.LineBundle.classOf N) :=
    (congrArg (A.IsHomogeneousPicardClass U) hc).mpr r₀.property
  obtain ⟨a, ha⟩ := AmpleDifferenceSurjectivity.Theta.Geometric.algebraic_ampleDifference_realizes_homogeneous_line A L N hL hN
  have hq : A.homogeneousPicardSheafInclusion.hom.app (.op U) q =
      (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) r.val :=
    (congrArg (A.homogeneousPicardSheafInclusion.hom.app (.op U)) hr).symm.trans
      (Picard.ThetaConstruction.HomogeneousBaseChangeForgetting.Geometric.homogeneousForget_toSheafify A U r)
  exact ⟨a, ha.trans ((congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)) hc).trans hq.symm)⟩

end AmpleTranslationGeometricPicard.Theta.Geometric

open _root_.CategoryTheory.Limits

variable {S : Scheme} [hS : IsAffine S] [IsLocallyNoetherian S] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g S} {L : Line.Bundles.LineBundle A.scheme.left}
    {P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme} (Q : Ample.TranslationQuotient.AmpleTranslationQuotient A L P)

include hS

theorem Ample.TranslationQuotient.AmpleTranslationQuotient.descendedDifference_geometric_surjective_algebraic
    (hL : L.IsAmple)
    {k : Type} [Field k] [IsAlgClosed k] (f : Spec (.of k) ⟶ S)
    (x : A.homogeneousPicardSheaf.obj.obj
      (.op ((Over.map f).obj (Over.mk (𝟙 (Spec (.of k))))))) :
    ∃ a : (Over.map f).obj (Over.mk (𝟙 (Spec (.of k)))) ⟶ Q.target.scheme,
      Q.descendedDifference.relativeValue a = A.homogeneousPicardSheafInclusion.hom.app
        (.op ((Over.map f).obj (Over.mk (𝟙 (Spec (.of k)))))) x := by
  let : IsAffineHom f := inferInstance
  let p := pullback.fst A.scheme.hom f
  let : IsAffineHom p := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback A.scheme.hom f).flip (inferInstance : IsAffineHom f)
  let Lf := L.pullback p
  have hLf : Lf.IsAmple := hL.pullback_of_isAffineHom p
  let U := Over.mk (𝟙 (Spec (.of k)))
  let x₀ : (A.pullback f).homogeneousPicardSheaf.obj.obj (.op U) :=
    (A.homogeneousPicardBaseChangeEquiv f U).symm x
  obtain ⟨a, ha⟩ := AmpleTranslationGeometricPicard.Theta.Geometric.algebraic_ampleDifference_surjective (A.pullback f) Lf hLf x₀
  let b := A.baseChangePointsEquiv f U a
  refine ⟨b ≫ Q.isogeny.hom, ?_⟩
  rw [Q.descendedDifference_value_pullback]
  have hbase : Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f U
      ((Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback f) Lf).relativeValue a) =
        (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue b :=
    Picard.ThetaConstruction.DifferenceBaseChangeValues.Geometric.relativeDifference_value_baseChange A L f U a
  have hforget := Picard.ThetaConstruction.HomogeneousBaseChangeForgetting.Geometric.homogeneousBaseChange_forget_at_algClosed A f (𝟙 (Spec (.of k))) x₀
  exact hbase.symm.trans ((congrArg (Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f U) ha).trans
    (hforget.symm.trans (congrArg
      (A.homogeneousPicardSheafInclusion.hom.app (.op ((Over.map f).obj U)))
      ((A.homogeneousPicardBaseChangeEquiv f U).apply_symm_apply x))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
