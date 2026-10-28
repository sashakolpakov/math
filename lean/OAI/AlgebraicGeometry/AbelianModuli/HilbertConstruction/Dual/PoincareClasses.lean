import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.PicardPoints

/-! # Poincare Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The tensor multiplication on the representing dual classifies actual Poincare pullbacks in the relative Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {g : ℕ} {S : Scheme.{u}} {A : Abelian.Schemes.AbelianScheme g S}

theorem Abelian.Schemes.AbelianScheme.homogeneousPicardSectionInclusion_toClass (A : Abelian.Schemes.AbelianScheme g S)
    (T : Over S) (q : A.homogeneousPicardPresheaf.obj (.op T)) :
    A.homogeneousPicardSectionInclusion T (A.toHomogeneousPicard.app (.op T) q) =
      (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) q.val :=
  (ConcreteCategory.congr_hom (CC := fun X : Type (u + 1) => X)
    (congr_app (toSheafify_naturality (Scheme.fppfTopology.over S) A.homogeneousPicardInclusion)
      (.op T)) q).symm

namespace Dual

def Data.DualAbelianData.poincareClass (D : Data.DualAbelianData A) : A.homogeneousPicardPresheaf.obj (.op D.abelian.scheme) :=
  ⟨Line.Bundles.LineBundle.classOf D.poincare, D.poincareHomogeneous⟩

def Data.DualAbelianData.poincareAt (D : Data.DualAbelianData A) {T : Over S} (x : T ⟶ D.abelian.scheme) :
    Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T) :=
  D.poincare.pullback ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map x)

theorem Data.DualAbelianData.pointClass_eq_poincare (D : Data.DualAbelianData A) {T : Over S} (x : T ⟶ D.abelian.scheme) :
    D.representable.homEquiv x = A.toHomogeneousPicard.app (.op T)
      (A.homogeneousPicardPresheaf.map x.op D.poincareClass) :=
  (D.representable.homEquiv_eq x).trans
    ((congrArg (fun z => A.homogeneousPicardSheaf.obj.map x.op z) D.universalClass).trans
      (A.toHomogeneousPicard.naturality_apply x.op D.poincareClass).symm)

theorem Data.DualAbelianData.pointRelativeClass_eq_poincare (D : Data.DualAbelianData A) {T : Over S}
    (x : T ⟶ D.abelian.scheme) :
    A.homogeneousPicardSectionInclusion T (D.representable.homEquiv x) =
      (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf (D.poincareAt x)) :=
  (congrArg (fun z => A.homogeneousPicardSectionInclusion T z) (D.pointClass_eq_poincare x)).trans
    (A.homogeneousPicardSectionInclusion_toClass T (A.homogeneousPicardPresheaf.map x.op D.poincareClass))

theorem Data.DualAbelianData.poincareAt_tensorProductPoint_class (D : Data.DualAbelianData A) {T : Over S}
    (x y : T ⟶ D.abelian.scheme) :
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf (D.poincareAt (D.tensorProductPoint x y))) =
      (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)
        (Line.Bundles.LineBundle.classOf ((D.poincareAt x).tensor (D.poincareAt y))) := by
  have h := congrArg (fun z => A.homogeneousPicardSectionInclusion T z) (D.tensorProductPoint_classifies x y)
  exact (D.pointRelativeClass_eq_poincare (D.tensorProductPoint x y)).symm.trans
    (h.trans (((A.homogeneousPicardSectionInclusion T).map_mul _ _).trans
      ((congrArg₂ (fun a b : Picard.PicardSheaf.PicardSections A.scheme T => a * b)
        (D.pointRelativeClass_eq_poincare x) (D.pointRelativeClass_eq_poincare y)).trans
          (Picard.SheafMonoid.toRelativePicard_mul A.scheme T (Line.Bundles.LineBundle.classOf (D.poincareAt x))
            (Line.Bundles.LineBundle.classOf (D.poincareAt y))).symm)))

end Dual

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
