import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.FamilyEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedPicardClasses

/-! # Family Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every homogeneous line bundle at an algebraically closed ground field is an actual Poincare specialization; tensoring by it preserves Euler characteristic. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}

theorem Dual.Data.DualAbelianData.homogeneous_is_poincare_at_algClosed (D : Dual.Data.DualAbelianData A)
    (M : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj (𝟙_ (Over (Spec (.of K))))))
    (hM : A.IsHomogeneousPicardClass (𝟙_ (Over (Spec (.of K)))) (Line.Bundles.LineBundle.classOf M)) :
    ∃ x : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme,
      Nonempty ((D.poincareAt x).sheaf ≅ M.sheaf) := by
  let q : A.homogeneousPicardPresheaf.obj (.op (𝟙_ (Over (Spec (.of K))))) :=
    ⟨Line.Bundles.LineBundle.classOf M, hM⟩
  obtain ⟨x, hx⟩ := D.representable.homEquiv.surjective (A.toHomogeneousPicard.app _ q)
  have h : (Picard.PicardSheaf.toRelativePicard A.scheme).app _ (Line.Bundles.LineBundle.classOf (D.poincareAt x)) =
      (Picard.PicardSheaf.toRelativePicard A.scheme).app _ (Line.Bundles.LineBundle.classOf M) :=
    (D.pointRelativeClass_eq_poincare x).symm.trans
      ((congrArg (A.homogeneousPicardSectionInclusion _) hx).trans
        (A.homogeneousPicardSectionInclusion_toClass _ q))
  exact ⟨x, ClosedPicardClasses.picard_bundle_iso_of_class_eq_at_algClosed A.scheme (𝟙 (Spec (.of K)))
    (D.poincareAt x) M h⟩

theorem Dual.Data.DualAbelianData.homogeneousFamily_twist_euler (D : Dual.Data.DualAbelianData A) (L : Line.Bundles.LineBundle A.scheme.left)
    (M : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj (𝟙_ (Over (Spec (.of K))))))
    (hM : A.IsHomogeneousPicardClass (𝟙_ (Over (Spec (.of K)))) (Line.Bundles.LineBundle.classOf M)) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (pullback.fst (𝟙 (Spec (.of K))) A.scheme.hom)
      (((L.pullback (pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom)).tensor M).sheaf) =
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (pullback.fst (𝟙 (Spec (.of K))) A.scheme.hom)
      (L.pullback (pullback.snd (𝟙 (Spec (.of K))) A.scheme.hom)).sheaf := by
  obtain ⟨x, ⟨e⟩⟩ := D.homogeneous_is_poincare_at_algClosed M hM
  exact (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso _
    (Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) e.symm)).trans (D.poincareFamily_twist_euler L x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
