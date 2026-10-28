import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectCoordinates
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios

/-! # Origin Path Defect Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.OriginPathDefectSymmetry

noncomputable section

/-! Commutation of the actual translation paths from the origin makes their regular defect symmetric. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberIsomorphismRatios

variable {k : Type u} [Field k] [IsAlgClosed k] {H A : Over (Spec (.of k))}
  [GrpObj H] [IsCommMonObj H] [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [IsIntegral A.left]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))
  (hc : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ H) (z : T ⟶ A)
    (hab : (a ≫ i) * (b ≫ i) = z) (hba : (b ≫ i) * (a ≫ i) = z),
    Subgroup.TranslationFibers.transportIso i L t (1 : T ⟶ A) (a ≫ i) a (mul_one (a ≫ i)) ≪≫ Subgroup.TranslationFibers.transportIso i L t (a ≫ i) z b hba =
      Subgroup.TranslationFibers.transportIso i L t (1 : T ⟶ A) (b ≫ i) b (mul_one (b ≫ i)) ≪≫ Subgroup.TranslationFibers.transportIso i L t (b ≫ i) z a hab)

include hc

/-- Properness transfers the proved origin commutation to the actual regular cocycle parameter on all test schemes. -/
theorem value_symmetric {T : Over (Spec (.of k))} (a b : T ⟶ H) :
    Subgroup.DefectParameters.value i L t a b = Subgroup.DefectParameters.value i L t b a := by
  let z := (a ≫ i) * (b ≫ i)
  have hba : (b ≫ i) * (a ≫ i) = z := mul_comm _ _
  have hd : ((a * b) ≫ i) * (1 : T ⟶ A) = z := by rw [mul_one, MonObj.mul_comp]
  have ha := Subgroup.DefectCoordinates.value_eq_defect i L t (1 : T ⟶ A) (a ≫ i) z a b (a * b)
    (mul_one (a ≫ i)) hba hd rfl
  have hb := Subgroup.DefectCoordinates.value_eq_defect i L t (1 : T ⟶ A) (b ≫ i) z b a (a * b)
    (mul_one (b ≫ i)) rfl hd (mul_comm b a)
  have hr := congrArg (fun f => Line.IsoRatios.ratio (FiberIsomorphismRatios.fiberLine L (1 : T ⟶ A)) f
    (Subgroup.TranslationFibers.transportIso i L t (1 : T ⟶ A) z (a * b) hd)) (hc T a b z rfl hba)
  exact (Subgroup.DefectParameters.defect_eq_value i L t a b (1 : T ⟶ A)).symm.trans
    (ha.trans (hr.trans (hb.symm.trans (Subgroup.DefectParameters.defect_eq_value i L t b a (1 : T ⟶ A)))))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.OriginPathDefectSymmetry
