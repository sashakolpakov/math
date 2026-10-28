import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianParameterComplex
import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.TrivialLevel
import OAI.ArithmeticGeometry.Descent.CMVariety.LocallyConstantFiber

/-! # Abelian Parameter -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! A constructed arithmetic parameter retaining the fixed CM tuple has
locally isomorphic fibers and yields the exact number-field group model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Topology

theorem SmoothAbelianFiber.SmoothAbelianParameter.cm_fiber_has_numberField_model
    {g : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : StandardModuli.Abelian.ComplexAbelianPresentation A) (E : AlgebraicEnhancement.Abelian.CMEnhancement P.variety)
    (D : SmoothAbelianFiber.SmoothAbelianParameter A (E.onPresentedFiber P)) : AbelianFiber.HasNumberFieldModel P.variety := by
  let : GrpObj P.variety.toOver := P.variety.group
  let G := D.nativeFamily
  let P₀ := D.nativeCenterPresentation P
  have hrec : ∀ i, P₀.comparison.inv ≫
      FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism D.nativeBase G (D.nativeExtraTuple.map i) D.nativeCenter ≫
        P₀.comparison.hom = E.map i :=
    @PresentedTupleComparison.Abelian.presented_tuple_recovery g (D.nativeFamily.pullback D.nativeCenter.left) A
      D.nativeCenterIso D.nativeCenterIso_group P E
      (D.nativeExtraTuple.pullback D.nativeCenter.left) D.native_extraRecovery
  have h := FamilyRigidity.Abelian.FamilyPoints.smooth_family_fixed_center_tuple_rigid G D.nativePresentation
    1 (by decide) (TrivialLevel.Abelian.trivialFullLevel G) D.nativeCenter P₀ E
    D.nativeExtraTuple.map D.nativeExtraTuple.group hrec
  apply LocallyConstantFiber.Abelian.abelian_fiber_descends_of_local_group_isomorphisms D.rationalStructure D.family D.point P.variety
  filter_upwards [h] with s hs
  obtain ⟨e, he, _, _⟩ := hs
  have : IsMonHom e.hom := he
  have hinv : IsMonHom e.inv := inferInstance
  have hcomp : IsMonHom (D.family.pullbackCompIso D.nativeProjection s.left).hom :=
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_preservesGroup D.family D.nativeProjection s.left
  let B := D.family.pullback (s.left ≫ D.nativeProjection)
  let c₁ := D.family.pullbackCompIso D.nativeProjection s.left ≪≫ e.symm
  have hc₁ : IsMonHom c₁.hom := AbelianEndomorphism.abelian_iso_trans_group B (G.pullback s.left)
    (G.pullback D.nativeCenter.left) (D.family.pullbackCompIso D.nativeProjection s.left)
    e.symm hcomp hinv
  let c₂ := c₁ ≪≫ D.nativeCenterIso
  have hc₂ : IsMonHom c₂.hom := AbelianEndomorphism.abelian_iso_trans_group B (G.pullback D.nativeCenter.left) A
    c₁ D.nativeCenterIso hc₁ D.nativeCenterIso_group
  let Q := @StandardModuli.Abelian.ComplexAbelianPresentation.transport g B A c₂ hc₂ P
  exact ⟨Q.comparison, Q.comparison_group⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety
