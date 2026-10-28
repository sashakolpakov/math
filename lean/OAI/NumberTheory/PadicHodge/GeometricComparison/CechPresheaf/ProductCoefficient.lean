import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientNaturality

/-! # Product Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ProductCoefficient.CechPresheafProductCoefficient

noncomputable section

/-! The original finite presheaf Cech coefficient isomorphism
commutes with actual tuple-product reindexing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v s t a b d e
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type d} [Category.{e} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : C ⥤ D) (G : A ⥤ B) [G.Additive] {ι : Type} [Finite ι] (U : ι → C)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ)

local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) F
local notation "KF" => Functor.obj (Functor.mapHomologicalComplex H (ComplexShape.up ℕ)) K
local notation "EU" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "EFU" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (Functor.obj F ∘ U)

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplex : TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U K).hom ≫
    (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso G EFU (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices (F.obj ∘ U)) K).hom =
      (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso G EU (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) KF).hom ≫
        (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex G K)).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact NonemptyCech.ProductCoefficient.NonemptyCechProductCoefficient.natural F G U (K.X q)

theorem total : (G.mapHomologicalComplex (.up ℕ)).map
    (HomologicalComplex₂.total.mapIso (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U K) (.up ℕ)).hom ≫
      (CoefficientTotal.CechPresheafCoefficientTotal.totalIso G EFU (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices (F.obj ∘ U)) K).hom =
    (CoefficientTotal.CechPresheafCoefficientTotal.totalIso G EU (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) KF).hom ≫
      (HomologicalComplex₂.total.mapIso
        (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex G K)) (.up ℕ)).hom := by
  let a := (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U K).hom
  have h₁ := IntegralComparison.InverseCoordinateHomology.inverse
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex EU KF))
    (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G (CoefficientTotal.CechPresheafCoefficientTotal.bicomplex EFU K))
    (HomologicalComplex₂.total.map (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G a) (.up ℕ))
    ((G.mapHomologicalComplex (.up ℕ)).map (HomologicalComplex₂.total.map a (.up ℕ)))
    (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.natural G a)
  let T := HomologicalComplex₂.totalFunctor B (.up ℕ) (.up ℕ) (.up ℕ)
  have h₂ := (T.map_comp (TotalCoefficientComposition.TotalCoefficientComparisonNaturality.bicomplexMap G a)
    (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso G EFU (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices (F.obj ∘ U)) K).hom).symm.trans
      ((congrArg T.map (bicomplex F G U K)).trans
        (T.map_comp (CoefficientTotal.CechPresheafCoefficientTotal.bicomplexIso G EU (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) KF).hom
          (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex G K)).hom))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ProductCoefficient.CechPresheafProductCoefficient
