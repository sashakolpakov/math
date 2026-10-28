import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.MapDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicFiberDegree

/-! # Intrinsic Finite Surjective -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.IntrinsicFiniteSurjective.Constructions.Intrinsic

noncomputable section

/-! A dominant finite etale map of integral complex schemes has positive
actual generic residue degree and surjects onto every native complex point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.MapDimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicFiberDegree.Constructions.Construction

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [IsIntegral Y.left]
  [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left]
  (hη : f.left (genericPoint X.left) = genericPoint Y.left)

include hη

theorem genericResidueDegree_pos : 0 < f.left.residueDegree (genericPoint X.left) := by
  let := (ProperImage.FunctionFields.Constructions.Construction.genericFieldMap f.left hη).hom.toAlgebra
  let := ProperImage.FunctionFields.Constructions.Construction.genericField_extension_finite f.left hη Y.hom (MapDimension.Constructions.integral_dominant_dimension f.left hη Y.hom)
  rw [← ProperImage.ResidueDegree.Constructions.Construction.genericFieldMap_finrank_eq_residueDegree f.left hη]
  exact Module.finrank_pos

variable [Etale f.left]

theorem nativeMap_surjective : Function.Surjective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  intro y
  have h : 0 < Nat.card {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X // ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x = y} := by
    rw [ProperImage.IntrinsicFiberDegree.Constructions.Construction.native_fiber_card_eq_residueDegree f hη y]
    exact genericResidueDegree_pos f hη
  obtain ⟨x⟩ := (Nat.card_pos_iff.mp h).1
  exact ⟨x.val, x.property⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.IntrinsicFiniteSurjective.Constructions.Intrinsic
