import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Approximation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.ResidueDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardPrescribedFiber
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Singular Order Approximation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SingularOrderApproximation

noncomputable section

/-! A principal divisor separates any one of finitely many divisor
points on an integral projective scheme, including singular schemes.
Its selected coefficient is the positive degree of an actual branch. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.DivisorComparison
  Affine.DivisorNorm

theorem exists_separating {X : Scheme} [IsIntegral X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) (S : Finset X) (x : X)
    (hS : ∀ z ∈ S, Order.coheight z = 1) :
    letI : AlgebraicGeometry.IsNoetherian X := P.isNoetherian
    ∃ (g : X.functionField) (d : ℕ), g ≠ 0 ∧ 0 < d ∧
      ∀ z ∈ S, (X.ord g z : ℚ) = if z = x then (d : ℚ) else 0 := by
  let : AlgebraicGeometry.IsNoetherian X := P.isNoetherian
  let : LocallyOfFiniteType f := P.finiteType.1
  let : IsFinite (Normalization.Scheme.normalizationMap X) := Normalization.Scheme.normalizationMap_isFinite X f
  let := Normalization.DivisorComparison.normalization_noetherian X f
  let T := (Normalization.Scheme.normalizationMap X) ⁻¹' (S : Set X)
  have hT : T.Finite := (Normalization.Scheme.normalizationMap X).finite_preimage S.finite_toSet
  let : Fintype T := hT.fintype
  obtain ⟨y, hy⟩ := Normalization.Scheme.normalizationMap_surjective X x
  have hheight (z : T) : Order.coheight (z.val : Normalization.Scheme.normalization X) = 1 := by
    rw [← Normalization.Height.normalizationMap_coheight X f z.val]
    exact hS _ z.property
  obtain ⟨g', hg', he⟩ := Normalization.Approximation.exists_orders P
    (fun z : T => z.val) hheight Subtype.val_injective (fun z => if z.val = y then 1 else 0)
  let g := (Normalization.Fields.normalizationFieldIso X).inv g'
  have hgg : (Normalization.Fields.normalizationFieldIso X).hom g = g' :=
    ConcreteCategory.congr_hom (Normalization.Fields.normalizationFieldIso X).inv_hom_id g'
  have hg : g ≠ 0 := by
    intro hz
    apply hg'
    rw [← hgg, hz, map_zero]
  refine ⟨g, (Normalization.Scheme.normalizationMap X).residueDegree y, hg,
    Normalization.ResidueDegree.positive X f y, ?_⟩
  intro z hz
  rw [← Normalization.DivisorComparison.normalization_divisor_coefficient X f z (hS z hz) g hg]
  have hc (w : Normalization.Scheme.normalization X) (hw : Normalization.Scheme.normalizationMap X w = z) :
      Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization X) ((Normalization.Fields.normalizationFieldIso X).hom g) w =
        if w = y then (1 : ℚ) else 0 := by
    have hwT : w ∈ T := by change Normalization.Scheme.normalizationMap X w ∈ S; rwa [hw]
    rw [hgg, Affine.DivisorNorm.rationalPrincipalDivisor_apply, he ⟨w, hwT⟩]
    split_ifs <;> norm_num
  rw [PushforwardPrescribedFiber.coefficient (Normalization.Scheme.normalizationMap X) _ y z 1 hc, hy, one_mul]
  simp only [eq_comm]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SingularOrderApproximation
