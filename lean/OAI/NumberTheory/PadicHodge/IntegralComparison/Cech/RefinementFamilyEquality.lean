import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Refinement
import Mathlib.Algebra.Homology.QuasiIso

/-! # Refinement Family Equality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementFamilyEquality.Family

noncomputable section

/-! Pointwise equal open families give the same refinement map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z
variable {C : Type u} [Preorder C] [HasBinaryProducts C]
  {A : Type v} [Category A] [Abelian A] [HasProducts.{w} A]
  {ι κ : Type w} {U U' : ι → C} {V V' : κ → C}
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (r' : FormalCoproduct.mk κ V' ⟶ FormalCoproduct.mk ι U') (P : Cᵒᵖ ⥤ A)

theorem quasiIso (hU : U = U') (hV : V = V') (hf : r.f = r'.f)
    [QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P)] :
    QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U' V' r' P) := by
  subst U'
  subst V'
  have hr : r = r' := FormalCoproduct.hom_ext hf (fun _ => Subsingleton.elim _ _)
  subst r'
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementFamilyEquality.Family
