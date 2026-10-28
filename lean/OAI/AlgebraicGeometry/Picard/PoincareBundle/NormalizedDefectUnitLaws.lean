import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectCocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TransportUnit

/-! # Normalized Defect Unit Laws -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedDefectUnitLaws

noncomputable section

/-! The actual regular translation cocycle is normalized at both subgroup identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationFibers
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TranslationDefect OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectCocycle OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.TransportUnit OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedTranslationUnit

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H A : Over (Spec (.of k))} [GrpObj H] [IsCommMonObj H] [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

theorem one_left {T : Over (Spec (.of k))} (a : T ⟶ H) :
    Subgroup.DefectParameters.value i L (NormalizedTranslationUnit.translation i L t) 1 a = 1 := by
  let x : T ⟶ A := 1
  let y := (a ≫ i) * x
  have hx : ((1 : T ⟶ H) ≫ i) * x = x := by rw [MonObj.one_comp, one_mul]
  have h := Subgroup.DefectCocycle.defect_eq_parameter i L (NormalizedTranslationUnit.translation i L t) x x y 1 a a hx rfl rfl (one_mul a)
  apply h.symm.trans
  apply (Subgroup.TranslationDefect.defect_eq_one_iff i L (NormalizedTranslationUnit.translation i L t) x x y 1 a a hx rfl rfl).mpr
  rw [Subgroup.TransportUnit.normalized_transport_unit i L t x hx, Iso.refl_trans]

theorem one_right {T : Over (Spec (.of k))} (a : T ⟶ H) :
    Subgroup.DefectParameters.value i L (NormalizedTranslationUnit.translation i L t) a 1 = 1 := by
  let x : T ⟶ A := 1
  let y := (a ≫ i) * x
  have hy : ((1 : T ⟶ H) ≫ i) * y = y := by rw [MonObj.one_comp, one_mul]
  have h := Subgroup.DefectCocycle.defect_eq_parameter i L (NormalizedTranslationUnit.translation i L t) x y y a 1 a rfl hy rfl (mul_one a)
  apply h.symm.trans
  apply (Subgroup.TranslationDefect.defect_eq_one_iff i L (NormalizedTranslationUnit.translation i L t) x y y a 1 a rfl hy rfl).mpr
  rw [Subgroup.TransportUnit.normalized_transport_unit i L t y hy, Iso.trans_refl]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedDefectUnitLaws
