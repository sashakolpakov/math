import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.NormalizationNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.PointSectionNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Zero Normalized Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! Zero-section normalization of an abelian-family line bundle commutes
with group isomorphisms and arbitrary changes of base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S T : Scheme.{u}} {g : ℕ} (A : Schemes.AbelianScheme g S)

def Schemes.AbelianScheme.zeroNormalizedBundle (L : Line.Bundles.LineBundle A.scheme.left) : Line.Bundles.LineBundle A.scheme.left :=
  Line.Bundles.LineBundle.sectionNormalized A.scheme.hom η[A.scheme].left L

def Schemes.AbelianScheme.zeroNormalizedBundle_zeroIso (L : Line.Bundles.LineBundle A.scheme.left) :
    ((A.zeroNormalizedBundle L).pullback η[A.scheme].left).sheaf ≅ Line.Bundles.structureModule S :=
  Line.Bundles.LineBundle.sectionNormalized_sectionIso A.scheme.hom η[A.scheme].left η[A.scheme].w L

theorem Schemes.AbelianScheme.pullback_zero_fst (f : T ⟶ S) :
    η[(A.pullback f).scheme].left ≫ pullback.fst A.scheme.hom f = f ≫ η[A.scheme].left := by
  change ((Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
    ((Over.pullback f).map η[A.scheme]).left) ≫ pullback.fst A.scheme.hom f = _
  rw [Category.assoc, Pullback.Comparisons.overPullback_map_left_fst, ← Category.assoc]
  erw [Family.PointSectionNaturality.pullbackUnitComparison_fst]

def Schemes.AbelianScheme.zeroNormalizedBundle_baseChangeIso (L : Line.Bundles.LineBundle A.scheme.left) (f : T ⟶ S) :
    ((A.zeroNormalizedBundle L).pullback (pullback.fst A.scheme.hom f)).sheaf ≅
      ((A.pullback f).zeroNormalizedBundle (L.pullback (pullback.fst A.scheme.hom f))).sheaf :=
  Line.Bundles.LineBundle.sectionNormalized_pullbackIso A.scheme.hom η[A.scheme].left
    (A.pullback f).scheme.hom η[(A.pullback f).scheme].left
    (pullback.fst A.scheme.hom f) f pullback.condition (A.pullback_zero_fst f) L

def Schemes.AbelianScheme.zeroNormalizedBundle_groupIso {B : Schemes.AbelianScheme g S}
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (L : Line.Bundles.LineBundle B.scheme.left) :
    ((B.zeroNormalizedBundle L).pullback e.hom.left).sheaf ≅
      (A.zeroNormalizedBundle (L.pullback e.hom.left)).sheaf :=
  Line.Bundles.LineBundle.sectionNormalized_pullbackIso B.scheme.hom η[B.scheme].left
    A.scheme.hom η[A.scheme].left e.hom.left (𝟙 S)
    (e.hom.w.trans (Category.comp_id _).symm)
    ((congrArg Over.Hom.left (IsMonHom.one_hom e.hom)).trans (Category.id_comp _).symm) L

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
