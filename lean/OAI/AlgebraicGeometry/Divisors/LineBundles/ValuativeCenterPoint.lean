import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.FractionField
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Valuative Center Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterPoint.BundleCycles.ValuativeCenter

noncomputable section

/-! Valuations of the actual function field have centers on a proper
scheme. The lifting diagram uses the given structure morphism and the
literal inclusion of the valuation ring in the function field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

theorem genericMap_scalar (f : X ⟶ Spec (.of k)) :
    Spec.map (CommRingCat.ofHom (Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap f)) = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X ≫ f := by
  obtain ⟨U, hU, hηU, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (genericPoint X))
  let : Nonempty U := ⟨⟨genericPoint X, hηU⟩⟩
  rw [← Foundations.Scheme.FunctionFieldScalar.specSectionScalarMap_germ f U, CommRingCat.ofHom_comp, Spec.map_comp,
    Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f U hU, ← Category.assoc]
  congr 1
  exact hU.fromSpecStalk_eq_fromSpecStalk hηU

theorem exists_generic_lift (f : X ⟶ Spec (.of k)) [IsProper f]
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra k R] [Algebra R X.functionField] [IsFractionRing R X.functionField]
    (hscalar : (algebraMap R X.functionField).comp (algebraMap k R) = Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap f) :
    ∃ i : Spec (.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ i = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X ∧
        i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
  have hp : ValuativeCriterion f := by
    have h : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  let sq : ValuativeCommSq f :=
    { R := R
      K := X.functionField
      i₁ := IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap k R))
      commSq := ⟨by
        rw [← genericMap_scalar, ← Spec.map_comp]
        exact congrArg (fun h : k →+* X.functionField => Spec.map (CommRingCat.ofHom h)) hscalar.symm⟩ }
  obtain ⟨i, hi₁, hi₂⟩ := (hp.existence sq).exists_lift
  exact ⟨i, hi₁, hi₂⟩

theorem lift_genericPoint (R : Type u) [CommRing R] [IsDomain R]
    [Algebra R X.functionField] [IsFractionRing R X.functionField]
    (i : Spec (.of R) ⟶ X)
    (hi : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ i = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X) :
    i (genericPoint (Spec (.of R))) = genericPoint X := by
  rw [← Affine.FractionField.BundleCycles.AffineFractionField.genericMap_genericPoint R X.functionField]
  change (Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ i) _ = _
  rw [hi]
  exact IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap_apply X _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterPoint.BundleCycles.ValuativeCenter
