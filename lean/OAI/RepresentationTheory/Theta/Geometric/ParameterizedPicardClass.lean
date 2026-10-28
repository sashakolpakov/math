import OAI.RepresentationTheory.Theta.Geometric.Picard.PicardPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf

/-! # Parameterized Picard Class -/

namespace OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass

noncomputable section

/-! An actual line bundle on a parameter product defines a natural
family of relative Picard classes. Its native zero-axis normalizations
are retained on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A P : Over S} (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left)

def parameterLineClass {T : Over S} (t : T ⟶ P) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (t ⊗ₘ 𝟙 A).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q)

theorem parameterLineClass_naturality {T U : Over S} (t : T ⟶ P) (f : U ⟶ T) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ⊗ₘ 𝟙 A).left (parameterLineClass Q t) =
      parameterLineClass Q (f ≫ t) := by
  rw [parameterLineClass, ← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have H : (f ⊗ₘ 𝟙 A) ≫ (t ⊗ₘ 𝟙 A) = (f ≫ t) ⊗ₘ 𝟙 A := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp]
  exact congrArg (fun h => AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass h (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
    (congrArg Over.Hom.left H)

def parameterPicardClass {T : Over S} (t : T ⟶ P) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A T :=
  (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (parameterLineClass Q t)

theorem parameterPicardClass_naturality {T U : Over S} (t : T ⟶ P) (f : U ⟶ T) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map f.op (parameterPicardClass Q t) =
      parameterPicardClass Q (f ≫ t) := by
  exact (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A f (parameterLineClass Q t)).trans
    (congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op U)) (parameterLineClass_naturality Q t f))

theorem parameterLineClass_baseChange {P' T : Over S} (p : P' ⟶ P) (t : T ⟶ P') :
    parameterLineClass Q (t ≫ p) = parameterLineClass (Q.pullback (p ⊗ₘ 𝟙 A).left) t :=
  (parameterLineClass_naturality Q p t).symm

theorem parameterLineClass_normalized [GrpObj A]
    (e : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    {T : Over S} (t : T ⟶ P) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A)).left (parameterLineClass Q t) = 1 := by
  have H : lift (𝟙 T) (1 : T ⟶ A) ≫ (t ⊗ₘ 𝟙 A) = t ≫ lift (𝟙 P) (1 : P ⟶ A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  change Picard.PicardPullback.picardPullback (lift (𝟙 T) (1 : T ⟶ A)).left
    (Picard.PicardPullback.picardPullback (t ⊗ₘ 𝟙 A).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q)) = 1
  rw [Picard.PicardPullback.picardPullback_comp, show (lift (𝟙 T) (1 : T ⟶ A)).left ≫ (t ⊗ₘ 𝟙 A).left =
    t.left ≫ (lift (𝟙 P) (1 : P ⟶ A)).left from congrArg Over.Hom.left H,
    ← Picard.PicardPullback.picardPullback_comp]
  have he : Picard.PicardPullback.picardPullback (lift (𝟙 P) (1 : P ⟶ A)).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) = 1 :=
    Quotient.sound ⟨e⟩
  rw [he, map_one]

theorem parameterLineClass_one [GrpObj P]
    (e : (Q.pullback (lift (1 : A ⟶ P) (𝟙 A)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (T : Over S) : parameterLineClass Q (1 : T ⟶ P) = 1 := by
  have H : (1 : T ⟶ P) ⊗ₘ 𝟙 A = snd T A ≫ lift (1 : A ⟶ P) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  change Picard.PicardPullback.picardPullback ((1 : T ⟶ P) ⊗ₘ 𝟙 A).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) = 1
  rw [show ((1 : T ⟶ P) ⊗ₘ 𝟙 A).left =
    (snd T A).left ≫ (lift (1 : A ⟶ P) (𝟙 A)).left from congrArg Over.Hom.left H,
    ← Picard.PicardPullback.picardPullback_comp]
  have he : Picard.PicardPullback.picardPullback (lift (1 : A ⟶ P) (𝟙 A)).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) = 1 :=
    Quotient.sound ⟨e⟩
  rw [he, map_one]

theorem parameterPicardClass_one [GrpObj P]
    (e : (Q.pullback (lift (1 : A ⟶ P) (𝟙 A)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (T : Over S) : parameterPicardClass Q (1 : T ⟶ P) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T :=
  congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T)) (parameterLineClass_one Q e T)

end

end OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass
