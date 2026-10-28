import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegralLineBundleMonomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.QuotientFiniteType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CohomologyEulerAdditivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EulerShifts

/-! # Section Cokernel Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionCokernelEuler

noncomputable section

/-! The actual cokernel of multiplication by a generically nonvanishing section has Euler characteristic equal to the difference of the two line-bundle Euler characteristics. For tensor powers, this is the first difference of the original Euler sequence. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (.of K)) [IsProper p] (L M : Line.Bundles.LineBundle X)

theorem lineBundleSectionCokernel_euler
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [Nonempty (Ample.LineBundles.sectionNonvanishing s)] :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (cokernel (SectionMultiplication.lineBundleSectionMultiply L M s)) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.tensor M).sheaf -
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M.sheaf := by
  have : M.sheaf.IsFiniteType := M.isFiniteType
  have : (L.tensor M).sheaf.IsFiniteType := (L.tensor M).isFiniteType
  have : M.sheaf.IsQuasicoherent := M.isQuasicoherent
  have : (L.tensor M).sheaf.IsQuasicoherent := (L.tensor M).isQuasicoherent
  let f := SectionMultiplication.lineBundleSectionMultiply L M s
  have : Mono f := IntegralLineBundleMonomorphisms.lineBundleSectionMultiply_mono L M s
  have : (cokernel f).IsQuasicoherent := Quasicoherent.Cokernels.module_quasicoherent_cokernel f
  have : (cokernel f).IsFiniteType := Quasicoherent.QuotientFiniteType.quasicoherent_cokernel_finiteType f
  let S : ShortComplex X.Modules :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact f⟩
  have h := Proper.CohomologyEulerAdditivity.proper_coherent_euler_additive p hS
  change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.tensor M).sheaf =
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M.sheaf +
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (cokernel f) at h
  change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (cokernel f) = _
  omega

omit [AlgebraicGeometry.IsIntegral X] [IsProper p] in
theorem lineBundle_tensor_succ_euler (m : ℕ) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.tensor (L.tensorPower m)).sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.tensorPower (m + 1)).sheaf := by
  have h : Line.Bundles.LineBundle.classOf (L.tensor (L.tensorPower m)) =
      Line.Bundles.LineBundle.classOf (L.tensorPower (m + 1)) := by
    rw [Line.Bundles.LineBundle.classOf_tensor, Line.Bundles.LineBundle.classOf_tensorPower,
      Line.Bundles.LineBundle.classOf_tensorPower, pow_succ']
  exact congrArg (EulerShifts.lineBundleClassEuler p) h

theorem lineBundleSectionCokernel_tensorPower_euler
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [Nonempty (Ample.LineBundles.sectionNonvanishing s)] (m : ℕ) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p
        (cokernel (SectionMultiplication.lineBundleSectionMultiply L (L.tensorPower m) s)) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.tensorPower (m + 1)).sheaf -
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.tensorPower m).sheaf := by
  rw [lineBundleSectionCokernel_euler p L (L.tensorPower m) s,
    lineBundle_tensor_succ_euler p L m]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionCokernelEuler
