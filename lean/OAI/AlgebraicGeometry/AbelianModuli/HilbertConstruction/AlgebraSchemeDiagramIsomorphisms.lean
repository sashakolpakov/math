import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSchemeDiagrams

/-! # Algebra Scheme Diagram Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSchemeDiagramIsomorphisms

noncomputable section

/-! Natural isomorphisms of coordinate algebras give natural isomorphisms of their affine schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

def algebraSchemeDiagramIso (C : Type u) [CommRing C]
    {J : Type v} [Category.{w} J] {A B : Jᵒᵖ ⥤ CommAlgCat.{u} C} (e : A ≅ B) :
    AlgebraSchemeDiagrams.algebraSchemeDiagram C B ≅ AlgebraSchemeDiagrams.algebraSchemeDiagram C A := by
  let eop : B.rightOp ≅ A.rightOp := {
    hom := e.hom.rightOp
    inv := e.inv.rightOp
    hom_inv_id := by rw [← NatTrans.rightOp_comp, e.inv_hom_id, NatTrans.rightOp_id]
    inv_hom_id := by rw [← NatTrans.rightOp_comp, e.hom_inv_id, NatTrans.rightOp_id] }
  exact Functor.isoWhiskerRight eop (algSpec (.of C))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSchemeDiagramIsomorphisms
