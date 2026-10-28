import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricDivision
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Marking
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareClass

/-! # Multiplication PEL Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Multiplication by a positive integer is an actual PEL isogeny
with squared polarization multiplier and the transported full marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareClass.PoincareClasses

variable {R k : Type} [CommRing R] [Field k] [CharZero k] [IsAlgClosed k] {g N : ℕ}
  (P : PEL.PELFamilyData R g N (Spec (.of k))) (n : ℕ)

omit [CharZero k] in
theorem MultiplicationPELIsogeny.multiplication_poincare :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 P.dual.abelian.scheme ⊗ₘ ((𝟙 P.abelian.scheme) ^ n)).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.dual.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (((𝟙 P.dual.abelian.scheme) ^ n) ⊗ₘ 𝟙 P.abelian.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.dual.poincare) := by
  let T := P.dual.abelian.scheme ⊗ P.abelian.scheme
  have : IsProper T.hom := by dsimp [T]; infer_instance
  have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  have : QuasiSeparatedSpace T.left := quasiSeparatedSpace_of_quasiSeparated T.hom
  have hr : 𝟙 P.dual.abelian.scheme ⊗ₘ ((𝟙 P.abelian.scheme) ^ n) =
      lift (fst P.dual.abelian.scheme P.abelian.scheme) ((snd P.dual.abelian.scheme P.abelian.scheme) ^ n) := by
    apply hom_ext <;> simp [MonObj.comp_pow]
  have hl : ((𝟙 P.dual.abelian.scheme) ^ n) ⊗ₘ 𝟙 P.abelian.scheme =
      lift ((fst P.dual.abelian.scheme P.abelian.scheme) ^ n) (snd P.dual.abelian.scheme P.abelian.scheme) := by
    apply hom_ext <;> simp [MonObj.comp_pow]
  rw [hr, hl]
  exact (PELModuli.IntegralModel.PoincareClass.PoincareClasses.pairClass_pow_right P.dual _ _ n).trans (PELModuli.IntegralModel.PoincareClass.PoincareClasses.pairClass_pow_left P.dual _ _ n).symm

variable [NeZero n] (hn : Nat.Coprime n N)

def PEL.PELFamilyData.multiplicationPELIsogeny : PELIsogenies.PELIsogeny P (P.shiftMarking (ZMod.unitOfCoprime n hn)) (n ^ 2) where
  isogeny := GeometricDivision.multiplicationIsogeny P.abelian n
  dualHom := (𝟙 P.dual.abelian.scheme) ^ n
  dualGroup := inferInstance
  poincare := MultiplicationPELIsogeny.multiplication_poincare P n
  equivariant r := by
    change End.endSchemeMap _ (P.action r) ≫ ((𝟙 P.abelian.scheme) ^ n) =
      ((𝟙 P.abelian.scheme) ^ n) ≫ End.endSchemeMap _ (P.action r)
    rw [MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp]
  polarization := by
    change ((𝟙 P.abelian.scheme) ^ n) ≫ P.polarizationMap.hom ≫
      ((𝟙 P.dual.abelian.scheme) ^ n) = P.polarizationMap.hom ^ (n ^ 2)
    rw [MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp, ← pow_mul, pow_two]
  marking T c := by
    change (P.marking.hom.app (.op T) c).val ≫ ((𝟙 P.abelian.scheme) ^ n) = _
    rw [MonObj.comp_pow, Category.comp_id, P.shiftMarking_q_points]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
