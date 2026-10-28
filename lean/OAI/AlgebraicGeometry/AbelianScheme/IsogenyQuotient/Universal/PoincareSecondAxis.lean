import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.PicardFaithfullyFlat
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard
import OAI.RepresentationTheory.Theta.Geometric.HomogeneousSheafInjection

/-! # Poincare Second Axis -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.PoincareSecondAxis.Construction

noncomputable section

/-! Universal source functions recover the second Poincare normalization
from its Picard origin and the first normalization over arbitrary bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

set_option backward.isDefEq.respectTransparency false in
theorem universal_poincare_dual_zero_of_origin
    {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme)
    (E : Over S) [GrpObj E] (J : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (E ⊗ A.scheme).left)
    (hJ : A.IsHomogeneousPicardClass E (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J))
    (z : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A E).left J).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule E.left)
    (ho : RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A J hJ (1 : 𝟙_ (Over S) ⟶ E) =
      A.trivialHomogeneousPicardClass (𝟙_ (Over S))) :
    Nonempty ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (lift (1 : A.scheme ⟶ E) (𝟙 A.scheme)).left J).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left) := by
  let T : Over S := 𝟙_ (Over S)
  let a : T ⟶ E := 1
  let K := J.pullback (a ▷ A.scheme).left
  let M := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial (T ⊗ A.scheme).left
  let eK := Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A a J z
  let eM : (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left M).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left :=
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left
  have hclass : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass J a = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K :=
    congrArg (fun m : T ⊗ A.scheme ⟶ E ⊗ A.scheme => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass m.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J))
      (tensorHom_id a A.scheme)
  have hp : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf K) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) := by
    exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)) hclass).symm.trans
      ((RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget A J hJ a).symm.trans
        ((congrArg (A.homogeneousPicardSheafInclusion.hom.app (.op T)) ho).trans
          (RepresentationTheory.Theta.Geometric.HomogeneousSheafInjection.homogeneousSheafClass_forget A T ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, A.trivialClass_homogeneous T⟩)))
  obtain ⟨e⟩ := BundleNormalization.Construction.universal_bundleIso_of_relativePicard_eq A.scheme T hA K M
    (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A T) (eK ≪≫ eM.symm) hp
  let v : A.scheme ⟶ T ⊗ A.scheme := (λ_ A.scheme).inv
  have hv : v ≫ (a ▷ A.scheme) = lift (1 : A.scheme ⟶ E) (𝟙 A.scheme) := by
    apply hom_ext
    · simp [v, a]
    · simp only [Category.assoc, whiskerRight_snd, lift_snd]
      exact leftUnitor_inv_snd A.scheme
  exact ⟨(Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hv)).symm.app J.sheaf ≪≫
    (Scheme.Modules.pullbackComp v.left (a ▷ A.scheme).left).symm.app J.sheaf ≪≫
    (Scheme.Modules.pullback v.left).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso v.left⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.PoincareSecondAxis.Construction
