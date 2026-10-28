import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedCoefficient

/-! # Refined Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinedCoefficient.CechAssemblyRefinedCoefficient

noncomputable section

/-! Actual projected Cech refinement preserves the original
coefficient comparison of an assembled complex-valued diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t a b d e
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : C ⥤ D) (G : A ⥤ B) [G.Additive]
  {ι κ : Type} [Finite ι] [Finite κ] (U : ι → C) (V : κ → D)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  (P : Dᵒᵖ ⥤ CochainComplex A ℕ)

theorem total : (G.mapHomologicalComplex (.up ℕ)).map
    (CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P)) ≫
      (CoefficientTotal.CechAssemblyCoefficientTotal.iso G (IntegralComparison.NonemptyCechNerve.nerve U)
        (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (F.op ⋙ P)).hom =
    (CoefficientTotal.CechAssemblyCoefficientTotal.iso G (IntegralComparison.NonemptyCechNerve.nerve V)
      (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices V) P).hom ≫
        CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r
          (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (P ⋙ G.mapHomologicalComplex (.up ℕ))) :=
  (congrArg (fun x => (G.mapHomologicalComplex (.up ℕ)).map
      (CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P)) ≫ x)
    (CoefficientCoordinates.CechAssemblyCoefficientCoordinates.hom G (IntegralComparison.NonemptyCechNerve.nerve U)
      (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (F.op ⋙ P))).trans
    ((CechPresheaf.RefinedCoefficient.CechPresheafRefinedCoefficient.total F G U V r (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P)).trans
      (congrArg (fun x => x ≫ CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r
        (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (P ⋙ G.mapHomologicalComplex (.up ℕ))))
        (CoefficientCoordinates.CechAssemblyCoefficientCoordinates.hom G (IntegralComparison.NonemptyCechNerve.nerve V)
          (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices V) P).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinedCoefficient.CechAssemblyRefinedCoefficient
