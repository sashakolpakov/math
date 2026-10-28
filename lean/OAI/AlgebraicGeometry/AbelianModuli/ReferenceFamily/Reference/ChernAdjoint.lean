import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.MarkedAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ComplexFibers

/-! # Chern Adjoint -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The constructed reference polarization has the original CM adjoints
on rational periods; its lattice isogeny is bijective on those periods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {z : P.domain}
    {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    {p : IsogenyKernel.ReferenceLatticeIsogeny M D} (C : PicardConstruction.ReferencePicardConstruction p)

instance PicardConstruction.ReferencePicardConstruction.referenceNativeIsogenyGroup :
    IsMonHom (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom) :=
  inferInstanceAs (IsMonHom p.isogeny.hom)

theorem PicardConstruction.ReferencePicardConstruction.chernForm_adjoint (a : NumberField.RingOfIntegers E) (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) x) y =
    Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver
        (M.functorAction (NumberField.IsCMField.ringOfIntegersComplexConj E a))) y) := by
  obtain ⟨u, rfl⟩ := M.nativeReferenceMarking.surjective x
  obtain ⟨v, rfl⟩ := M.nativeReferenceMarking.surjective y
  rw [M.nativeReferenceMarking_action, M.nativeReferenceMarking_action, C.chern, C.chern]
  unfold Datum.RankThreePELDatum.traceForm
  congr 1
  exact NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.trace_rosati _ _ _ _ _

theorem PicardConstruction.ReferencePicardConstruction.chernForm_left_ext (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian)
    (h : ∀ w, Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x w = Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine y w) : x = y := by
  apply sub_eq_zero.mp
  apply Intrinsic.ChernPeriod.nativeChernForm_separating M.abelian C.ampleLine C.ample
  intro w
  change (Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine (x - y)) w = 0
  rw [map_sub, LinearMap.sub_apply, h w, sub_self]

theorem PicardConstruction.ReferencePicardConstruction.latticeIsogeny_period_bijective :
    Function.Bijective (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ D.abelian.toOver from p.isogeny.hom)) := by
  let f : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom
  let : IsFinite f.left := inferInstanceAs (IsFinite p.isogeny.hom.left)
  have hf := Finite.ComplexFibers.NativeLinearMaps.rationalLift_injective_of_isFinite f
  have hd : Module.finrank ℚ (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) = Module.finrank ℚ (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods D.abelian) := by
    rw [Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank, Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank, M.dimension, D.dimension]
  exact ((Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f).linearEquivOfInjective hf hd).bijective

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
