import OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteOpenDescent
import Mathlib.RingTheory.Algebraic.Basic

/-! # Field Component Descent -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.FieldComponentDescent.Construction

noncomputable section

/-! Descent of geometric component opens through finite algebraic coefficient fields. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

universe u

theorem algebraic_coefficient_isField
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (s : Finset L) : IsField (CoefficientSystem.Constructions.Foundations.coefficientRing k L s) :=
  (CoefficientSystem.Constructions.Foundations.coefficientRing k L s).isField_of_algebraic

theorem algebraic_coefficient_finite
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (s : Finset L) : Module.Finite k (CoefficientSystem.Constructions.Foundations.coefficientRing k L s) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
    (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)

theorem smooth_proper_components_descend_to_coefficient_field
    (k L : Type u) [Field k] [Field L] [IsAlgClosed L]
    [Algebra k L] [Algebra.IsAlgebraic k L]
    (s : Finset L) (X : Over (CoefficientSystem.Constructions.Foundations.coefficientBase k L s))
    [Smooth X.hom] [IsProper X.hom] :
    ∃ (j : Over (op s)), Base.Construction.HasSplitGeometricComponents
      (Over.mk (pullback.fst (CoefficientSystem.Constructions.Foundations.coefficientBaseMap k L (leOfHom j.hom.unop)) X.hom)) := by
  let q := pullback.fst (CoefficientSystem.Constructions.Foundations.genericBaseMap k L s) X.hom
  let G : Over (Spec (.of L)) := Over.mk q
  have : Smooth G.hom := inferInstanceAs (Smooth (pullback.fst _ X.hom))
  have : IsProper G.hom := inferInstanceAs (IsProper (pullback.fst _ X.hom))
  obtain ⟨n, U, hdis, hcover, hconn⟩ := GeometricFieldComponents.Construction.smooth_proper_split_components_over_algClosed G
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsNoetherian G.left := ⟨⟩
  let U' : Fin n → (Descent.Constructions.Foundations.expansionCone k L s X).pt.Opens := U
  have hn : NoetherianSpace (Descent.Constructions.Foundations.expansionCone k L s X).pt :=
    inferInstanceAs (NoetherianSpace G.left)
  obtain ⟨j, V, hpre⟩ := FiniteOpenDescent.Construction.finite_compact_opens_descend k L s X U'
    (fun _ ↦ NoetherianSpace.isCompact _)
  let : Field (CoefficientSystem.Constructions.Foundations.coefficientRing k L j.left.unop) :=
    (algebraic_coefficient_isField k L j.left.unop).toField
  refine ⟨j, ?_⟩
  exact FiniteOpenDescent.Construction.split_components_of_cartesian_opens (FiniteOpenDescent.Construction.expansion_stage_cartesian k L s X j)
    n U V hpre hdis hcover hconn

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.FieldComponentDescent.Construction
