import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

/-! # Pushforward Composition -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardComposition

noncomputable section

section

/-! Extracting the prescribed codimension component commutes with native
point pushforward. Nonzero residue degree forces equal support dimensions,
so all discarded source components also disappear in the target degree. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Grading

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Fields

theorem dimension_eq_of_finite_genericField {k : Type} [Field k]
    {S T : Scheme.{0}} [IsIntegral S] [IsIntegral T]
    (i : S ⟶ T) (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ Spec (.of k)) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη).hom.toAlgebra
    Module.Finite T.functionField S.functionField →
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη).hom.toAlgebra
  intro hf
  let := hf
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ g)
  let : IsScalarTower k T.functionField S.functionField := IsScalarTower.of_algHom (Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom i hη g)
  have h := trdeg_add_eq k T.functionField (A := S.functionField)
  rw [trdeg_eq_zero (R := T.functionField) (A := S.functionField), add_zero] at h
  exact congrArg Cardinal.toNat h

theorem support_dimension_eq_of_degree {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (A : IrreducibleCloseds X.carrier)
    (hdeg : f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint A) ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f A) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.structureMap := by
  let := (Support.Fields.supportFunctionFieldMap f A).hom.toAlgebra
  have hpos : 0 < Module.finrank (CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f A)).functionField
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).functionField := by
    rw [Support.Fields.supportFunctionField_finrank_eq]
    exact Nat.pos_of_ne_zero hdeg
  have hf := Module.finite_of_finrank_pos hpos
  have h := dimension_eq_of_finite_genericField (Support.Map.supportImageMap f A)
    (Support.Map.supportImageMap_genericPoint f A) (CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f A) Y.structureMap) hf
  rw [Support.Map.supportImageMap_over] at h
  exact h

theorem cyclePushforward_supportInDegree {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (m n p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (hdeg : p + n = q + m) (A : IrreducibleCloseds X.carrier) :
    ProperCycleLinearity.cyclePushforward f p q (CycleClass.Thom.IntersectionGeometry.supportInDegree X p A) =
      (f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint A) : ℚ) • CycleClass.Thom.IntersectionGeometry.supportInDegree Y q (ProperCycleLinearity.imageSupport f A) := by
  by_cases hA : X.supportCodimension A = p
  · rw [CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_left hA]
    simpa only [one_smul, ProperCycleLinearity.cyclePushforwardGenerator] using
      (ProperCycleLinearity.cyclePushforward_single f p q (⟨A, hA⟩ : X.DimensionCycleSupport p) 1)
  · rw [CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_right hA, map_zero]
    by_cases hz : f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint A) = 0
    · rw [hz, Nat.cast_zero, zero_smul]
    · have himage : Y.supportCodimension (ProperCycleLinearity.imageSupport f A) ≠ q := by
        intro hb
        have hd := support_dimension_eq_of_degree f A hz
        have hx := Grading.supportDimension_add_codimension X m A
        have hy := Grading.supportDimension_add_codimension Y n (ProperCycleLinearity.imageSupport f A)
        rw [hb] at hy
        omega
      rw [CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_right himage, smul_zero]

theorem degreeComponent_single (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) (x : X.carrier) (a : ℚ) :
    CyclePushforward.degreeComponent X p (Finsupp.single x a) = a • CycleClass.Thom.IntersectionGeometry.supportInDegree X p (irreducibleSetEquivPoints.symm x) := by
  rw [CyclePushforward.degreeComponent, Finsupp.linearCombination_single]

/-- The actual graded cycle pushforward is obtained by taking the target
degree of native point pushforward, even before the source is projected. -/
theorem cyclePushforward_degreeComponent {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (m n p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (hdeg : p + n = q + m) (c : X.carrier →₀ ℚ) :
    ProperCycleLinearity.cyclePushforward f p q (CyclePushforward.degreeComponent X p c) =
      CyclePushforward.degreeComponent Y q (CyclePushforward.pointPushforward (show X.carrier ⟶ Y.carrier from f.left) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single x a =>
    rw [degreeComponent_single, map_smul, cyclePushforward_supportInDegree f m n p q hdeg,
      CyclePushforward.pointPushforward_single, degreeComponent_single, smul_smul]
    exact congrArg (fun z : X.carrier => (a * (f.left.residueDegree z : ℚ)) •
      CycleClass.Thom.IntersectionGeometry.supportInDegree Y q (irreducibleSetEquivPoints.symm (f.left z)))
        (irreducibleSetEquivPoints.apply_symm_apply x)

end Grading

end

/-! Composition of the genuine graded cycle pushforwards follows from
composition at generic points and the proved compatibility with grading. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

theorem cycle_comp {X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (g : Y.toOver ⟶ Z.toOver) (n k p q r : ℕ)
    [SmoothOfRelativeDimension n Y.structureMap]
    [SmoothOfRelativeDimension k Z.structureMap]
    (hg : q + k = r + n) (a : X.RationalDimensionCycle p) :
    ProperCycleLinearity.cyclePushforward g q r (ProperCycleLinearity.cyclePushforward f p q a) = ProperCycleLinearity.cyclePushforward (f ≫ g) p r a := by
  rw [CyclePushforward.cyclePushforward_eq_pointPushforward f p q]
  change ProperCycleLinearity.cyclePushforward g q r (CyclePushforward.degreeComponent Y q (CyclePushforward.pointPushforward f.left (CyclePushforward.pointCycle X p a))) = _
  rw [Grading.cyclePushforward_degreeComponent g n k q r hg]
  have hcomp := DFunLike.congr_fun (CyclePushforward.pointPushforward_comp f.left g.left).symm (CyclePushforward.pointCycle X p a)
  change CyclePushforward.pointPushforward g.left (CyclePushforward.pointPushforward f.left (CyclePushforward.pointCycle X p a)) =
    CyclePushforward.pointPushforward (f.left ≫ g.left) (CyclePushforward.pointCycle X p a) at hcomp
  change CyclePushforward.degreeComponent Z r (CyclePushforward.pointPushforward g.left (CyclePushforward.pointPushforward f.left (CyclePushforward.pointCycle X p a))) = _
  rw [hcomp, CyclePushforward.cyclePushforward_eq_pointPushforward (f ≫ g) p r]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardComposition
