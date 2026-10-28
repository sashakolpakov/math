import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClosedSheafification

/-! # Homogeneous Base Change Forgetting -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.HomogeneousBaseChangeForgetting.Geometric

noncomputable section

/-! At an actual algebraically closed field test, homogeneous Picard
base change commutes with forgetting homogeneity. Sheafification is
computed using the proved comparison at that original field test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem homogeneousForget_toSheafify (U : Over S)
    (q : A.homogeneousPicardPresheaf.obj (.op U)) :
    A.homogeneousPicardSheafInclusion.hom.app (.op U)
      ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op U) q) =
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) q.val :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Scheme.fppfTopology.over S) A.homogeneousPicardInclusion) (.op U)) q).symm

theorem homogeneousBaseChange_forget_at_algClosed {S' : Scheme} (f : S' ⟶ S)
    {K : Type} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S')
    (q : (A.pullback f).homogeneousPicardSheaf.obj.obj (.op (Over.mk s))) :
    A.homogeneousPicardSheafInclusion.hom.app (.op ((Over.map f).obj (Over.mk s)))
      (A.homogeneousPicardBaseChangeEquiv f (Over.mk s) q) =
        AbelianModuli.HilbertConstruction.Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f (Over.mk s)
          ((A.pullback f).homogeneousPicardSheafInclusion.hom.app (.op (Over.mk s)) q) := by
  obtain ⟨r, rfl⟩ := (AbelianModuli.ReferenceFamily.ClosedSheafification.fppf_toSheafify_bijective_at_algClosed s
    (A.pullback f).homogeneousPicardPresheaf).surjective q
  rw [A.toHomogeneousPicard_baseChange_apply, homogeneousForget_toSheafify,
    homogeneousForget_toSheafify]
  exact (AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme f (Over.mk s) r.val).symm

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.HomogeneousBaseChangeForgetting.Geometric
