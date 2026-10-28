import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedTensorDomain
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ProductChart
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalFiber
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Closed Geometric Integral -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedGeometricIntegral

noncomputable section

/-! An integral finite type scheme over an algebraically closed field is
geometrically irreducible. For smooth schemes this also gives geometric
integrality, so products with singular integral supports remain integral. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical TensorProduct

theorem baseChange_irreducible {K L : Type} [Field K] [IsAlgClosed K] [Field L]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (g : Spec (.of L) ⟶ Spec (.of K)) : IrreducibleSpace ↥(pullback f g) := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (Opens.mem_top (genericPoint X))
  let : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  let V : (Spec (.of L)).Opens := ⊤
  have hV : IsAffineOpen V := isAffineOpen_top _
  let : Nonempty V := ⟨⟨genericPoint (Spec (.of L)), trivial⟩⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra g V
  let : Algebra.FiniteType K Γ(X, U) := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let : IsDomain (Γ(X, U) ⊗[K] Γ(Spec (.of L), V)) :=
    ClosedTensorDomain.isDomain
  let j := Affine.ProductChart.map f g U hU V hV
  have hi : IsIrreducible (Set.range j) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Spec (.of (Γ(X, U) ⊗[K] Γ(Spec (.of L), V))))).image
        j j.continuous.continuousOn
  have hd : Dense (Set.range j) := by
    rw [Affine.ProductChart.range]
    simpa only [V, Opens.coe_top, Set.preimage_univ, Set.inter_univ] using
      (U.isOpen.dense ⟨genericPoint X, hxU⟩).preimage (pullback.fst f g).isOpenMap
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set ↥(pullback f g))
  simpa only [hd.closure_eq] using hi.closure

theorem geometricallyIrreducible {K : Type} [Field K] [IsAlgClosed K]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    GeometricallyIrreducible f :=
  ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun _ _ g => baseChange_irreducible f g⟩

theorem geometricallyIntegral {K : Type} [Field K] [IsAlgClosed K]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of K)) [Smooth f] :
    GeometricallyIntegral f := by
  let : GeometricallyIrreducible f := geometricallyIrreducible f
  let : GeometricallyReduced f := ProjectionFormula.Smooth.LocalFiber.geometricallyReduced f
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedGeometricIntegral
