import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceLineTranslation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.FamilySheafMaps

/-! # Reference Line Values -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceLineValues.Geometric

noncomputable section

/-! Original line-class values in the relative Picard sheaf are
natural in both test schemes and actual group families, and commute
with the actual base-change equivalence. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.FamilySheafMaps

variable {S : Scheme.{0}} {g h : ℕ}

def originalLineValue (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left) (U : Over S) :
    AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme U :=
  (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left q)

theorem originalLineValue_naturality (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left) {U V : Over S} (u : V ⟶ U) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map u.op (originalLineValue A q U) = originalLineValue A q V := by
  apply (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme u _).trans
  apply congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op V))
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (u ⊗ₘ 𝟙 A.scheme).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left q) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd V A.scheme).left q
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  exact congrArg (fun t => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t q)
    (congrArg Over.Hom.left ((tensorHom_snd u (𝟙 A.scheme)).trans (Category.comp_id _)))

theorem originalLineValue_baseChange (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.scheme.left) {S' : Scheme.{0}} (b : S' ⟶ S) (U : Over S') :
    AbelianModuli.HilbertConstruction.Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme b U
      (originalLineValue (A.pullback b) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (CategoryTheory.Limits.pullback.fst A.scheme.hom b) q) U) =
      originalLineValue A q ((Over.map b).obj U) := by
  refine Quotient.inductionOn q (fun L => ?_)
  exact (AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme b U _).trans
    (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op ((Over.map b).obj U)))
      (ReferenceLineTranslation.Geometric.originalLineFamily_baseChange_class A b U L))

theorem constantLineClass_familyMap (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (f : A.scheme ⟶ B.scheme) (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.scheme.left) (U : Over S) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 U ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U B.scheme).left q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q) := by
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  exact congrArg (fun t => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t q)
    (congrArg Over.Hom.left (tensorHom_snd (𝟙 U) f))

theorem originalLineValue_familyMap (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (f : A.scheme ⟶ B.scheme) (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.scheme.left) (U : Over S) :
    (AbelianModuli.HilbertConstruction.Picard.FamilySheafMaps.relativePicardSheafMap f).hom.app (.op U) (originalLineValue B q U) =
      originalLineValue A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q) U :=
  (AbelianModuli.HilbertConstruction.Picard.FamilySheafMaps.relativePicardSheafMap_toRelative f U _).trans
    (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)) (constantLineClass_familyMap A B f q U))

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceLineValues.Geometric
