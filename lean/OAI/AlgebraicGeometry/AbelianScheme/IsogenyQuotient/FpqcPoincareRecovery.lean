import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcHomogeneousPicard
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcPicardOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.PoincareSecondAxis

/-! # Fpqc Poincare Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcPoincareRecovery.Construction

noncomputable section

/-! An actual recovered Poincare line suffices for full dual-data
descent. Normalization, homogeneity, the Picard origin, and the second
normalization are constructed from recovery across the fpqc cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S Y : Scheme.{0}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Y}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (hB : GlobalFunctions.Construction.HasUniversalGlobalFunctions B.scheme) (u : Y ⟶ S)
    [Flat u] [Surjective u] [QuasiCompact u]
    (eA : A.scheme ≅ (B.pullback u).scheme) [IsMonHom eA.hom]
    (E : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (eD : D.abelian.scheme ≅ (E.pullback u).scheme)
    (q : (Over.map u).obj D.abelian.scheme ⟶ E.scheme)
    (hq : q.left = AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u D.abelian.scheme E.scheme eD)
    (J : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (E.scheme ⊗ B.scheme).left)
    (hr : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ B.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.ReferenceFamily.PoincareFixed.fixedFamilyPoincare D B u eA))

include hB hq hr in
set_option backward.isDefEq.respectTransparency false in
theorem fpqc_recoveredPoincare_homogeneous :
    B.IsHomogeneousPicardClass E.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) := by
  have hp : IsPullback D.abelian.scheme.hom q.left u E.scheme.hom := by
    rw [hq]
    exact AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap_isPullback u D.abelian.scheme E.scheme eD
  have : Flat q.left := MorphismProperty.of_isPullback (P := @Flat) hp inferInstance
  have : Surjective q.left := MorphismProperty.of_isPullback (P := @Surjective) hp inferInstance
  have : QuasiCompact q.left := MorphismProperty.of_isPullback (P := @QuasiCompact) hp inferInstance
  apply FpqcHomogeneousPicard.Construction.homogeneousPicardClass_of_fpqc_pullback B hB q (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J)
  change B.IsHomogeneousPicardClass ((Over.map u).obj D.abelian.scheme)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ B.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J))
  rw [hr]
  exact AbelianModuli.ReferenceFamily.PoincareFixed.fixedFamilyPoincare_homogeneous D B u eA

include hr in
omit [Flat u] [Surjective u] [QuasiCompact u] in
set_option backward.isDefEq.respectTransparency false in
theorem normalized_recoveredPoincare_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ B.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle B.scheme E.scheme J)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.ReferenceFamily.PoincareFixed.fixedFamilyPoincare D B u eA) := by
  rw [FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class, ← tensorHom_id q B.scheme,
    FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_pullback, tensorHom_id, hr]
  exact FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_of_axis B.scheme _ _
    (Quotient.sound ⟨AbelianModuli.ReferenceFamily.PoincareFixed.fixedFamilyPoincare_zeroIso D B u eA⟩)

def fpqcDualDataOfRecoveredPoincare [IsMonHom eD.hom] : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B := by
  let J' := FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle B.scheme E.scheme J
  have hr' : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ B.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J') =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.ReferenceFamily.PoincareFixed.fixedFamilyPoincare D B u eA) :=
    normalized_recoveredPoincare_class D B u eA E q J hr
  have hJ' := fpqc_recoveredPoincare_homogeneous D B hB u eA E eD q hq J' hr'
  let zB := FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis B.scheme E.scheme J
  have hz := FpqcPicardOrigin.Construction.fpqc_descendedPicard_parameter_origin D B u eA E eD q hq J' hJ' hr' hB
    (𝟙_ (Over S))
  let zE := (Universal.PoincareSecondAxis.Construction.universal_poincare_dual_zero_of_origin B hB E.scheme J' hJ' zB hz).some
  exact FpqcDualData.Construction.fpqcDescendedDualData D B hB u eA E eD q hq J' hJ' hr' zB zE

theorem fpqcDualDataOfRecoveredPoincare_abelian [IsMonHom eD.hom] :
    (fpqcDualDataOfRecoveredPoincare D B hB u eA E eD q hq J hr).abelian = E := rfl

theorem fpqcDualDataOfRecoveredPoincare_recovery [IsMonHom eD.hom] :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ B.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (fpqcDualDataOfRecoveredPoincare D B hB u eA E eD q hq J hr).poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.ReferenceFamily.PoincareFixed.fixedFamilyPoincare D B u eA) :=
  normalized_recoveredPoincare_class D B u eA E q J hr

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcPoincareRecovery.Construction
