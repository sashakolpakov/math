import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcParameterClassification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardCoverBijection

/-! # Fpqc Dual Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcDualData.Construction

noncomputable section

/-! Full native Picard dual data descend through an arbitrary faithfully
flat quasi-compact base change once their actual Poincare line and its
normalizations have descended. No finite-presentation assumption on
the base extension is required. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DescendedPicardCoverBijection

variable {S Y : Scheme.{0}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Y}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (hB : GlobalFunctions.Construction.HasUniversalGlobalFunctions B.scheme) (u : Y ⟶ S)
    [Flat u] [Surjective u] [QuasiCompact u]
    (eA : A.scheme ≅ (B.pullback u).scheme) [IsMonHom eA.hom]
    (E : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (eD : D.abelian.scheme ≅ (E.pullback u).scheme)
    (q : (Over.map u).obj D.abelian.scheme ⟶ E.scheme)
    (hq : q.left = AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u D.abelian.scheme E.scheme eD)
    (J : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (E.scheme ⊗ B.scheme).left)
    (hJ : B.IsHomogeneousPicardClass E.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J))
    (hr : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ B.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.ReferenceFamily.PoincareFixed.fixedFamilyPoincare D B u eA))

include hB hq hr in
theorem fpqc_descendedPicard_parameterMap_isIso : IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap B J hJ) := by
  apply FpqcParameterClassification.Construction.fpqc_parameterMap_isIso u (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap B J hJ)
  · intro T
    have hb := AbelianModuli.ReferenceFamily.DescendedPicardCoverBijection.descendedPicard_parameter_bijective_over_cover D B u eA E.scheme eD q hq J hJ hr T
    constructor
    · intro a b hab
      apply ULift.ext
      exact hb.injective hab
    · intro x
      obtain ⟨a, ha⟩ := hb.surjective x
      exact ⟨ULift.up a, ha⟩
  · exact Picard.BaseCoverInjection.Construction.homogeneousPicard_baseCoverRestriction_injective u B hB

def fpqcDescendedPicardRepresentable : B.homogeneousPicardSheaf.obj.RepresentableBy E.scheme := by
  have : IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap B J hJ) :=
    fpqc_descendedPicard_parameterMap_isIso D B hB u eA E eD q hq J hJ hr
  exact (Functor.RepresentableBy.equivUliftYonedaIso B.homogeneousPicardSheaf.obj E.scheme).symm
    (asIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap B J hJ))

def fpqcDescendedDualData
    (zB : (J.pullback (lift (𝟙 E.scheme) (1 : E.scheme ⟶ B.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule E.scheme.left)
    (zE : (J.pullback (lift (1 : B.scheme ⟶ E.scheme) (𝟙 B.scheme)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left) : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B where
  abelian := E
  representable := fpqcDescendedPicardRepresentable D B hB u eA E eD q hq J hJ hr
  origin T := RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_one B J hJ zE T
  poincare := J
  poincareHomogeneous := hJ
  universalClass := AbelianModuli.ReferenceFamily.HomogeneousParameterRecovery.homogeneousParameterClass_identity B E.scheme J hJ
  normalizedAtAbelianZero := ⟨zB⟩
  normalizedAtDualZero := ⟨zE⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcDualData.Construction
