import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.NormalizedLineOpenDescent
import OAI.RepresentationTheory.Theta.Geometric.HomogeneousSheafInjection

/-! # Poincare Second Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PoincareSecondZero

noncomputable section

/-! For a locally Noetherian abelian family, the actual second
Poincare normalization follows from the represented origin and the
first normalization. The parameter tests need not be Noetherian. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.RepresentationTheory.Theta.Geometric.HomogeneousSheafInjection OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

/-- The first rigidification removes the possible base twist in the
line represented by the dual origin. -/
theorem normalizedPoincare_dualZero_of_origin
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (E : Over S) [GrpObj E] (J : Line.Bundles.LineBundle (E ⊗ A.scheme).left)
    (hJ : A.IsHomogeneousPicardClass E (Line.Bundles.LineBundle.classOf J))
    (z : (J.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A E).left).sheaf ≅ Line.Bundles.structureModule E.left)
    (ho : RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A J hJ (1 : 𝟙_ (Over S) ⟶ E) =
      A.trivialHomogeneousPicardClass (𝟙_ (Over S))) :
    Nonempty ((J.pullback (lift (1 : A.scheme ⟶ E) (𝟙 A.scheme)).left).sheaf ≅
      Line.Bundles.structureModule A.scheme.left) := by
  let T : Over S := 𝟙_ (Over S)
  let a : T ⟶ E := 1
  let K := J.pullback (a ▷ A.scheme).left
  let M := Line.Bundles.LineBundle.trivial (T ⊗ A.scheme).left
  let eK := Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A a J z
  let eM : (M.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).sheaf ≅ Line.Bundles.structureModule T.left :=
    Line.Bundles.structureModulePullbackIso (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
  have hclass : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass J a = Line.Bundles.LineBundle.classOf K :=
    congrArg (fun m : T ⊗ A.scheme ⟶ E ⊗ A.scheme => Line.Bundles.LineBundle.pullbackClass m.left (Line.Bundles.LineBundle.classOf J))
      (tensorHom_id a A.scheme)
  have hp : (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf K) =
      (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.classOf M) := by
    exact (congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)) hclass).symm.trans
      ((RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget A J hJ a).symm.trans
        ((congrArg (A.homogeneousPicardSheafInclusion.hom.app (.op T)) ho).trans
          (RepresentationTheory.Theta.Geometric.HomogeneousSheafInjection.homogeneousSheafClass_forget A T ⟨Line.Bundles.LineBundle.trivialClass _, A.trivialClass_homogeneous T⟩)))
  obtain ⟨e⟩ := A.bundleIso_of_relativePicard_eq T K M eK eM hp
  let v : A.scheme ⟶ T ⊗ A.scheme := (λ_ A.scheme).inv
  have hv : v ≫ (a ▷ A.scheme) = lift (1 : A.scheme ⟶ E) (𝟙 A.scheme) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [v, a]
    · simp only [Category.assoc, whiskerRight_snd, lift_snd]
      exact leftUnitor_inv_snd A.scheme
  exact ⟨(Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hv)).symm.app J.sheaf ≪≫
    (Scheme.Modules.pullbackComp v.left (a ▷ A.scheme).left).symm.app J.sheaf ≪≫
    (Scheme.Modules.pullback v.left).mapIso e ≪≫ Line.Bundles.structureModulePullbackIso v.left⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PoincareSecondZero
