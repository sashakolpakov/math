import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.SquareNormalization

/-! # Total Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.TotalNaturality

noncomputable section

/-! Canonical constant-module sections commute with the original
finite Čech total coefficient map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z r s
variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]

local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R (OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections.constantUnit R J) 0

abbrev unit : (ModuleCat.uliftFunctor.{z,w} R) ⟶ (constantSheaf J (ModuleCat.{w} R)) ⋙ E :=
  GeometricComparison.ConstantExt.ConstantExtSectionTransformation.unit R J

theorem sectionMap (M : CochainComplex (ModuleCat.{w} R) ℕ)
    (K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ)
    (a : (((constantSheaf J (ModuleCat.{w} R))).mapHomologicalComplex (.up ℕ)).obj M ⟶ K) :
    ComplexMap.map R J M K a =
      ((unit R J).mapHomologicalComplex (.up ℕ)).app M ≫
        ((E).mapHomologicalComplex (.up ℕ)).map a := by
  rfl

variable {D : Type r} [Category.{s} D] [HasBinaryProducts D]
  [HasProducts.{0} (Sheaf J (ModuleCat.{w} R))]
  [HasCoproducts.{0} (Sheaf J (ModuleCat.{w} R))]
  {ι : Type} [Finite ι] (U : ι → D)
  (Q : Dᵒᵖ ⥤ CochainComplex (ModuleCat.{w} R) ℕ)
  (P : Dᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ)
  (a : Q ⋙ (constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ) ⟶ P)

omit [HasBinaryProducts D] [HasProducts.{0} (Sheaf J (ModuleCat.{w} R))]
    [HasCoproducts.{0} (Sheaf J (ModuleCat.{w} R))] in
theorem diagram : GeometricComparison.CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.diagramMap (constantSheaf J (ModuleCat.{w} R)) (ModuleCat.uliftFunctor.{z,w} R) E Q P a (unit R J) =
    GeometricComparison.ConstantExt.ConstantExtSectionTransformation.transformation R J Q P a := by
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.TotalNaturality
