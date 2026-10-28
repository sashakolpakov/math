import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme

/-! # Reduced Product -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ReducedProduct.Constructions

noncomputable section

/-! The actual reduced cycle of a product support has one irreducible
component of multiplicity one. The grading still uses its genuine
algebraic codimension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : LocallyOfFiniteType X.toOver.hom :=
  inferInstanceAs (LocallyOfFiniteType X.structureMap)

theorem closedComponentSupport_of_irreducible (X : Scheme) (S : Closeds X)
    (I : IrreducibleCloseds X) (hI : (I : Set X) = (S : Set X))
    (C : irreducibleComponents S) : IntersectionGeometry.closedComponentSupport X S C = I := by
  let : IrreducibleSpace S := isIrreducible_iff_irreducibleSpace.mp (hI ▸ I.isIrreducible)
  have hC : C.val = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using C.property
  apply IrreducibleCloseds.ext
  change Subtype.val '' C.val = (I : Set X)
  rw [hC, Set.image_univ, Subtype.range_coe, hI]

theorem reducedClosedCycle_irreducible (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (S : Closeds X.carrier) (I : IrreducibleCloseds X.carrier)
    (hI : (I : Set X.carrier) = (S : Set X.carrier)) :
    IntersectionGeometry.reducedClosedCycle X p S = IntersectionGeometry.supportInDegree X p I := by
  classical
  let : IrreducibleSpace S := isIrreducible_iff_irreducibleSpace.mp (hI ▸ I.isIrreducible)
  let C : irreducibleComponents S := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]
    exact Set.mem_singleton _⟩
  ext W
  rw [IntersectionGeometry.reducedClosedCycle_apply, IntersectionGeometry.supportInDegree_apply]
  have he : (∃ T : irreducibleComponents S, IntersectionGeometry.closedComponentSupport X.carrier S T = W.val) ↔ I = W.val := by
    constructor
    · rintro ⟨T, hT⟩
      rwa [closedComponentSupport_of_irreducible X.carrier S I hI T] at hT
    · intro h
      exact ⟨C, (closedComponentSupport_of_irreducible X.carrier S I hI C).trans h⟩
  rw [he]

theorem reducedProductCycle_eq_supportInDegree
    (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (p : ℕ)
    (A : IrreducibleCloseds X.carrier) (B : IrreducibleCloseds Y.carrier) :
    IntersectionGeometry.reducedClosedCycle Z p (IntersectionGeometry.productClosedSupport X Y Z πX πY A B) =
    IntersectionGeometry.supportInDegree Z p (Product.SupportScheme.Constructions.productIrreducibleSupport X.toOver Y.toOver A B Z.toOver πX πY hprod) :=
  reducedClosedCycle_irreducible Z p (IntersectionGeometry.productClosedSupport X Y Z πX πY A B)
    (Product.SupportScheme.Constructions.productIrreducibleSupport X.toOver Y.toOver A B Z.toOver πX πY hprod)
    (Product.SupportScheme.Constructions.productIrreducibleSupport_coe X.toOver Y.toOver A B Z.toOver πX πY hprod)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ReducedProduct.Constructions
