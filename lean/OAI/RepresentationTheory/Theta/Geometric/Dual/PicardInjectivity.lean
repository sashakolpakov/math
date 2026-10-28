import OAI.RepresentationTheory.Theta.Geometric.DescendedPicardHomomorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts

/-! # Picard Injectivity -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.PicardInjectivity

noncomputable section

/-! Complex-point separation and a trivial native infinitesimal kernel
give injectivity on all actual dual-number parameters of a Picard group
homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem parameterPicardClass_dual_injective_of_hom {A P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left)
    (ρ : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P) →* AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ))
    (hρ : ∀ t, ρ t = ParameterizedPicardClass.parameterPicardClass Q t)
    (hcomplex : Function.Injective (fun t : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P => ParameterizedPicardClass.parameterPicardClass Q t))
    (hkernel : ∀ v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints P 1,
      ParameterizedPicardClass.parameterPicardClass Q v.val = ParameterizedPicardClass.parameterPicardClass Q
        (1 : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P) → v.val = 1) :
    Function.Injective (fun t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t) := by
  intro a b hab
  have hbase : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ≫ a = AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ≫ b := by
    apply hcomplex
    exact (ParameterizedPicardClass.parameterPicardClass_naturality Q a (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ)).symm.trans
      ((congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ).op) hab).trans
        (ParameterizedPicardClass.parameterPicardClass_naturality Q b (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ)))
  let red : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P) →* AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P :=
    { toFun := fun f => AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ ≫ f
      map_one' := MonObj.comp_one _
      map_mul' := fun f g => MonObj.comp_mul _ f g }
  let v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints P 1 := ⟨a * b⁻¹, by
    change red (a * b⁻¹) = 1
    rw [map_mul, map_inv, show red a = red b from hbase, mul_inv_cancel]⟩
  have hρab : ρ a = ρ b := (hρ a).trans (hab.trans (hρ b).symm)
  have hv : ρ v.val = ρ 1 := by
    change ρ (a * b⁻¹) = ρ 1
    rw [map_mul, map_inv, map_one, hρab, mul_inv_cancel]
  exact mul_inv_eq_one.mp (hkernel v ((hρ v.val).symm.trans (hv.trans (hρ 1))))

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.PicardInjectivity
