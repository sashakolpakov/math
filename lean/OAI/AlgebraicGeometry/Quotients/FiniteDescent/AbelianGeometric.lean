import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupIrreducibleOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Abelian Geometric -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianGeometric.Construction.AbelianGeometricIntegral

noncomputable section

/-! A proper smooth geometrically connected commutative group over a
field is geometrically integral. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K] (A : Over (Spec (.of K)))
variable [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom]
variable [GeometricallyConnected A.hom]

theorem geometricallyIntegral : GeometricallyIntegral A.hom := by
  constructor
  intro L _ t Z p q h
  let B := (Over.pullback t).obj A
  let : GrpObj B := Functor.grpObjObj
  have : IsCommMonObj B := inferInstanceAs (IsCommMonObj ((Over.pullback t).obj A))
  have : IsProper B.hom := by dsimp [B]; infer_instance
  have : Smooth B.hom := by dsimp [B]; infer_instance
  have : GeometricallyConnected B.hom := by dsimp [B]; infer_instance
  have : IrreducibleSpace B.left := GroupIrreducibleOf.Construction.GroupIrreducible.irreducibleSpace_over_field B
  have : IsReduced B.left := SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field B.hom
  have : IsIntegral (pullback A.hom t) := isIntegral_of_irreducibleSpace_of_isReduced B.left
  exact IsIntegral.of_isIso h.isoPullback.inv

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianGeometric.Construction.AbelianGeometricIntegral
