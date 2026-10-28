import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.OneComponentHomology

/-! # Refinement One Edge -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.RefinementOneEdge.CechRefinementHOneEdge

noncomputable section

/-! A degree-one edge square gives the original typed H-one
refinement square without comparing whole cochain maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t a b
variable (R : Type u) [CommRing R]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {D : Type a} [Category.{b} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  (K : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ)
  {M : CochainComplex (ModuleCat.{max u v} R) ℕ}
  (e : M ⟶ CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.total R V K)
  (p : M ⟶ CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.total R U
    (((CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.pullback R F).mapHomologicalComplex (.up ℕ)).obj K))
  (h : e.f 1 ≫ (CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r K).f 1 = p.f 1)

include h in
theorem homology : HomologicalComplex.homologyMap e 1 ≫
    CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.refinementHOne R F U V r K = HomologicalComplex.homologyMap p 1 :=
  (HomologicalComplex.homologyMap_comp _ _ 1).symm.trans
    (CechPresheaf.ComponentHomology.CechPresheafComponentHomology.homology_of_component _ _ 1 h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.RefinementOneEdge.CechRefinementHOneEdge
