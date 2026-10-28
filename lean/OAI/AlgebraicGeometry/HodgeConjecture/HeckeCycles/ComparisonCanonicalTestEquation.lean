import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BranchEnumeration
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TestEquation

/-! # Comparison Canonical Test Equation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonCanonicalTestEquation.CM.Tate

/-! Descend the original TateComparison action along any epimorphic geometric
test, including the canonical arithmetic test of a common evaluation
field. Actual branch labels retain every endpoint and multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (t : AbelianScheme.TateComparison.Local.IntegralType s) (f : D.EndK)
  {T : Over (Spec (.of K))} {F : Type} [Field F] [IsAlgClosed F]
  (b : Spec (.of F) ⟶ Spec (.of K)) (p : Over.mk b ⟶ T) [Epi p]
  (i : Fin D.componentCount) (x y : T ⟶ D.componentGeneric i)
  {I J : Type} [Fintype I] [Fintype J]
  (ex : I ≃ (D.correspondence t).Fiber (x ≫ D.componentInclusion i))
  (ey : J ≃ (D.correspondence t).Fiber (y ≫ D.componentInclusion i))
  (ex' : I ≃ (D.correspondence t).Fiber (p ≫ (x ≫ D.componentInclusion i)))
  (ey' : J ≃ (D.correspondence t).Fiber (p ≫ (y ≫ D.componentInclusion i)))

include ex' ey' in
theorem point_equation (hpoints : TateComparisonPointEquation.CM.Raw.RawAction D hg t f) :
    Source.TestEquation.CM.PointEquation D hg T f
      (x ≫ D.componentInclusion i) (y ≫ D.componentInclusion i)
      (Finset.univ.val.map (fun a => (D.correspondence t).endpoint (ex a)))
      (Finset.univ.val.map (fun a => (D.correspondence t).endpoint (ey a))) := by
  apply PointSpecializationFormula.CM.Descent.neighbor_formula_of_precompose D.albaneseGroup p (D.albaneseMap hg) f
    (x ≫ D.componentInclusion i) (y ≫ D.componentInclusion i)
  have h := TateComparisonPointEvaluation.CM.raw_equation_evaluated D hg
    b t f i (p ≫ x) (p ≫ y)
    (hpoints F b i (p ≫ x) (p ≫ y))
  have hx := Finite.BranchEnumeration.CM.neighbors_eq_original_targets
    (D.correspondence t) (x ≫ D.componentInclusion i) ex
    b (p) ex'
  have hy := Finite.BranchEnumeration.CM.neighbors_eq_original_targets
    (D.correspondence t) (y ≫ D.componentInclusion i) ey
    b (p) ey'
  simp only [AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.neighbors, Category.assoc] at h
  rw [hx, hy] at h
  simpa only [AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.aPoint, AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.aTotalPoint,
    Multiset.map_map, Function.comp_def, Category.assoc] using h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonCanonicalTestEquation.CM.Tate

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonCanonicalTestEquation.CM.TateSource

/-! Descend the original TateComparison action along any epimorphic geometric
test, including the canonical arithmetic test of a common evaluation
field. Actual branch labels retain every endpoint and multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (t : AbelianScheme.TateComparison.Local.IntegralType s) (f : D.EndK)
  {T : Over (Spec (.of K))} {F : Type} [Field F] [IsAlgClosed F]
  (b : Spec (.of F) ⟶ Spec (.of K)) (p : Over.mk b ⟶ T) [Epi p]
  (i : Fin D.componentCount) (x y : T ⟶ D.componentGeneric i)
  {I J : Type} [Fintype I] [Fintype J]
  (zx zy : T ⟶ D.space)
  (hx : zx = x ≫ D.componentInclusion i) (hy : zy = y ≫ D.componentInclusion i)
  (ex : I ≃ (D.correspondence t).Fiber zx)
  (ey : J ≃ (D.correspondence t).Fiber zy)
  (ex' : I ≃ (D.correspondence t).Fiber (p ≫ zx))
  (ey' : J ≃ (D.correspondence t).Fiber (p ≫ zy))

include hx hy ex' ey' in
theorem point_equation (hpoints : TateComparisonPointEquation.CM.Raw.RawAction D hg t f) :
    Source.TestEquation.CM.PointEquation D hg T f zx zy
      (Finset.univ.val.map (fun a => (D.correspondence t).endpoint (ex a)))
      (Finset.univ.val.map (fun a => (D.correspondence t).endpoint (ey a))) := by
  subst zx
  subst zy
  exact Tate.point_equation D hg t f b p i x y ex ey ex' ey' hpoints

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonCanonicalTestEquation.CM.TateSource

end

end OAI
