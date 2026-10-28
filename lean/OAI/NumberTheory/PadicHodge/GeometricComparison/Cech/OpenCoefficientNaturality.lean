import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.OpenBaseChangeNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality

/-! # Open Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.OpenCoefficientNaturality.CechOpenCoefficientNaturality

noncomputable section

/-! The canonical Čech comparison for inverse-image opens commutes with additive coefficient change. -/

open _root_.CategoryTheory Limits Opposite Simplicial

universe w v u vD uD vA uA vB uB

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasFiniteProducts D]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{w} B]
  (F : C ⥤ D) [PreservesFiniteLimits F]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{w, w} G]
  {ι : Type w} (U : ι → C) (P : Dᵒᵖ ⥤ A)

theorem naturality :
    (G.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).hom ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι (F.obj ∘ U)).cech P).hom =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech (F.op ⋙ P)).hom ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U (P ⋙ G)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  let E := (FormalCoproduct.mk ι U).cech
  let D := (FormalCoproduct.mk ι (F.obj ∘ U)).cech
  let b := (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P).hom.f n
  let c := (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U (P ⋙ G)).hom.f n
  have h : G.map b ≫ piComparison G (fun t : (D.obj (op ⦋n⦌)).I => P.obj (op ((D.obj (op ⦋n⦌)).obj t))) =
      piComparison G (fun t : (E.obj (op ⦋n⦌)).I => P.obj (op (F.obj ((E.obj (op ⦋n⦌)).obj t)))) ≫ c :=
    AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.piComparison_map G
      (fun t : Fin (n + 1) → ι => P.map (PreservesProduct.iso F (U ∘ t)).symm.op.hom)
  exact (congrArg (fun k => G.map b ≫ k) (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f G D P n)).trans
    (h.trans (congrArg (fun k => k ≫ c) (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.hom_f G E (F.op ⋙ P) n).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.OpenCoefficientNaturality.CechOpenCoefficientNaturality
