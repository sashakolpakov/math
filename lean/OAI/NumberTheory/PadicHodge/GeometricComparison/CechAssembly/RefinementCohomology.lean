import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.TotalFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.OneComponentHomology

/-! # Refinement Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinementCohomology.CechAssemblyRefinementHOne

noncomputable section

/-! Refinement H-one and comparison naturality in the actual
assembled diagram coordinates before and after precomposition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t a b
variable (R : Type u) [CommRing R]
  {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {D : Type a} [Category.{b} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  (P : Dᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ)

def mapHOne : (CoefficientTotal.CechAssemblyCoefficientTotal.total (IntegralComparison.NonemptyCechNerve.nerve V) P).homology 1 ⟶
    (CoefficientTotal.CechAssemblyCoefficientTotal.total (IntegralComparison.NonemptyCechNerve.nerve U) (F.op ⋙ P)).homology 1 :=
  HomologicalComplex.homologyMap (CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P)) 1

variable {L : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  (f : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P ⟶ L)
  (g : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (F.op ⋙ P) ⟶
    ((CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.pullback R F).mapHomologicalComplex (.up ℕ)).obj L)
  (h : ∀ q, q ≤ 1 → ∀ W,
    ((((CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.pullback R F).mapHomologicalComplex (.up ℕ)).map f).f q).app W =
      (g.f q).app W)

include h in
theorem comparison : CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R V f ≫
    CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.refinementHOne R F U V r L =
      mapHOne R F U V r P ≫ CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U g :=
  CechPresheaf.OneComponentHomology.CechPresheafHOneComponentHomology.refinement_homology R U F V r f g h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinementCohomology.CechAssemblyRefinementHOne
