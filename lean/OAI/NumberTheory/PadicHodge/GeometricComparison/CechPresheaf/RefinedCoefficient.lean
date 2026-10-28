import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedFactorization
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ProductCoefficient

/-! # Refined Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedCoefficient.CechPresheafRefinedCoefficient

noncomputable section

/-! Additive coefficient change commutes with the actual projected
refinement of the original presheaf Cech total. -/

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
  (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ)

local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := A) F
local notation "KF" => Functor.obj (Functor.mapHomologicalComplex H (ComplexShape.up ℕ)) K

theorem total : (G.mapHomologicalComplex (.up ℕ)).map (RefinedReindex.CechPresheafRefinedReindex.map F U V r K) ≫
    (CoefficientTotal.CechPresheafCoefficientTotal.totalIso G (IntegralComparison.NonemptyCechNerve.nerve U)
      (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) KF).hom =
    (CoefficientTotal.CechPresheafCoefficientTotal.totalIso G (IntegralComparison.NonemptyCechNerve.nerve V)
      (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices V) K).hom ≫
        RefinedReindex.CechPresheafRefinedReindex.map F U V r (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex G K) := by
  let T := G.mapHomologicalComplex (.up ℕ)
  let e := HomologicalComplex₂.total.mapIso (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U K) (.up ℕ)
  let e' := HomologicalComplex₂.total.mapIso
    (NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso F U (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex G K)) (.up ℕ)
  let c₀ := (CoefficientTotal.CechPresheafCoefficientTotal.totalIso G (IntegralComparison.NonemptyCechNerve.nerve V)
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices V) K).hom
  let c₁ := (CoefficientTotal.CechPresheafCoefficientTotal.totalIso G (IntegralComparison.NonemptyCechNerve.nerve (F.obj ∘ U))
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices (F.obj ∘ U)) K).hom
  let c₂ := (CoefficientTotal.CechPresheafCoefficientTotal.totalIso G (IntegralComparison.NonemptyCechNerve.nerve U)
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) KF).hom
  let a := RefinementCoefficient.CechPresheafRefinementCoefficient.map V (F.obj ∘ U) r K
  let b := RefinementCoefficient.CechPresheafRefinementCoefficient.map V (F.obj ∘ U) r (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex G K)
  have hInv : T.map e.inv ≫ c₂ = c₁ ≫ e'.inv :=
    (IntegralComparison.InverseCoordinateHomology.inverse (T.mapIso e) e' c₂ c₁
      (ProductCoefficient.CechPresheafProductCoefficient.total F G U K).symm).symm
  have hRef : T.map a ≫ c₁ = c₀ ≫ b := RefinementCoefficient.CechPresheafRefinementCoefficient.total G V (F.obj ∘ U) r K
  have hMid : T.map (a ≫ e.inv) ≫ c₂ = c₀ ≫ (b ≫ e'.inv) :=
    (congrArg (fun q => q ≫ c₂) (T.map_comp a e.inv)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun q => T.map a ≫ q) hInv).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q => q ≫ e'.inv) hRef).trans (Category.assoc _ _ _)))))
  exact (congrArg (fun q => T.map q ≫ c₂) (RefinedFactorization.CechPresheafRefinedFactorization.total F U V r K)).trans
    (hMid.trans (congrArg (fun q => c₀ ≫ q)
      (RefinedFactorization.CechPresheafRefinedFactorization.total F U V r (CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex G K))).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedCoefficient.CechPresheafRefinedCoefficient
