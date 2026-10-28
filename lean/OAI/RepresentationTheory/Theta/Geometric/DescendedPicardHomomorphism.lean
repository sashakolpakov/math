import OAI.RepresentationTheory.Theta.Geometric.TestDifferenceHomomorphism
import OAI.RepresentationTheory.Theta.Geometric.FppfPairLift

/-! # Descended Picard Homomorphism -/

namespace OAI.RepresentationTheory.Theta.Geometric.DescendedPicardHomomorphism

noncomputable section

/-! The descended native Picard family is additive on every test
scheme, by simultaneous fppf lifting to the original cubical family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {d : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {B : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj B]
    (p : A.scheme ⟶ B) [IsMonHom p] [Flat p.left] [LocallyOfFinitePresentation p.left] [Surjective p.left]
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hcube : ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (x y z : T ⟶ A.scheme),
      Picard.PicardPullback.picardPullback (x * y * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback x.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) * Picard.PicardPullback.picardPullback y.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback z.left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
        Picard.PicardPullback.picardPullback (x * y).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback (x * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
          Picard.PicardPullback.picardPullback (y * z).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B ⊗ A.scheme).left)
    (recover : (Q.pullback (p ⊗ₘ 𝟙 A.scheme).left).sheaf ≅ (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf)

include recover in
omit [GrpObj B] [IsMonHom p] [Flat p.left] [LocallyOfFinitePresentation p.left] [Surjective p.left] in
theorem descendedParameterPicardClass_lift {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (a : T ⟶ A.scheme) :
    ParameterizedPicardClass.parameterPicardClass Q (a ≫ p) = TestDifferenceHomomorphism.parameterDifferencePicardHom A L hcube T a := by
  have H := (ParameterizedPicardClass.parameterLineClass_baseChange Q p a).trans
    (DifferencePicardClasses.parameterLineClass_congr _ _ recover a)
  exact congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)) H

include p L hcube recover in
theorem descendedParameterPicardClass_mul {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (a b : T ⟶ B) :
    ParameterizedPicardClass.parameterPicardClass Q (a * b) = ParameterizedPicardClass.parameterPicardClass Q a * ParameterizedPicardClass.parameterPicardClass Q b := by
  obtain ⟨U, u, x, y, huF, huP, huS, hxa, hyb⟩ := FppfPairLift.exists_fppf_pair_lift p a b
  let : Flat u.left := huF
  let : LocallyOfFinitePresentation u.left := huP
  let : Surjective u.left := huS
  apply FppfPicardLocality.fppfSheaf_map_injective (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme) u
  have hxy : u ≫ (a * b) = (x * y) ≫ p := by
    rw [MonObj.comp_mul, hxa, hyb, MonObj.mul_comp]
  calc
    _ = ParameterizedPicardClass.parameterPicardClass Q (u ≫ (a * b)) := ParameterizedPicardClass.parameterPicardClass_naturality Q (a * b) u
    _ = ParameterizedPicardClass.parameterPicardClass Q ((x * y) ≫ p) := congrArg (ParameterizedPicardClass.parameterPicardClass Q) hxy
    _ = TestDifferenceHomomorphism.parameterDifferencePicardHom A L hcube U (x * y) :=
      descendedParameterPicardClass_lift A p L hcube Q recover (x * y)
    _ = TestDifferenceHomomorphism.parameterDifferencePicardHom A L hcube U x * TestDifferenceHomomorphism.parameterDifferencePicardHom A L hcube U y :=
      (TestDifferenceHomomorphism.parameterDifferencePicardHom A L hcube U).map_mul x y
    _ = ParameterizedPicardClass.parameterPicardClass Q (x ≫ p) * ParameterizedPicardClass.parameterPicardClass Q (y ≫ p) :=
      congrArg₂ (· * ·) (descendedParameterPicardClass_lift A p L hcube Q recover x).symm
        (descendedParameterPicardClass_lift A p L hcube Q recover y).symm
    _ = ParameterizedPicardClass.parameterPicardClass Q (u ≫ a) * ParameterizedPicardClass.parameterPicardClass Q (u ≫ b) := by rw [hxa, hyb]
    _ = (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map u.op (ParameterizedPicardClass.parameterPicardClass Q a) *
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map u.op (ParameterizedPicardClass.parameterPicardClass Q b) :=
      congrArg₂ (· * ·) (ParameterizedPicardClass.parameterPicardClass_naturality Q a u).symm
        (ParameterizedPicardClass.parameterPicardClass_naturality Q b u).symm
    _ = _ := by
      simpa only [AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup.Construction.relativePicardRestrictHom_apply] using
        ((AlgebraicGeometry.Picard.Homomorphisms.RelativeGroup.Construction.relativePicardRestrictHom A.scheme u).map_mul
          (ParameterizedPicardClass.parameterPicardClass Q a) (ParameterizedPicardClass.parameterPicardClass Q b)).symm

def descendedParameterPicardHom (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) : (T ⟶ B) →* AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme T where
  toFun := ParameterizedPicardClass.parameterPicardClass Q
  map_one' := by
    have h := descendedParameterPicardClass_mul A p L hcube Q recover (1 : T ⟶ B) 1
    rw [one_mul] at h
    exact (mul_left_cancel ((mul_one _).trans h)).symm
  map_mul' := descendedParameterPicardClass_mul A p L hcube Q recover

end

end OAI.RepresentationTheory.Theta.Geometric.DescendedPicardHomomorphism
