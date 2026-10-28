import OAI.RepresentationTheory.Theta.Geometric.Reference.PolarizationConstruction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.MarkedAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ComplexFibers

/-! # Chern Adjoint -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference

noncomputable section

/-! The original ample Chern form has the exact CM adjoints on native
rational periods. The original lattice isogeny is bijective on those periods. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} (C : PolarizationConstruction.ReferencePolarizationConstruction p)

theorem PolarizationConstruction.ReferencePolarizationConstruction.chernForm_adjoint (a : NumberField.RingOfIntegers E)
    (x y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) x) y =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver
          (M.functorAction (NumberField.IsCMField.ringOfIntegersComplexConj E a))) y) := by
  obtain ⟨u, rfl⟩ := M.nativeReferenceMarking.surjective x
  obtain ⟨v, rfl⟩ := M.nativeReferenceMarking.surjective y
  rw [M.nativeReferenceMarking_action, M.nativeReferenceMarking_action, C.chern, C.chern]
  unfold AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.traceForm
  congr 1
  exact NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.trace_rosati _ _ _ _ _

theorem PolarizationConstruction.ReferencePolarizationConstruction.chernForm_left_ext (x y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian)
    (h : ∀ w, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x w =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine y w) : x = y := by
  apply sub_eq_zero.mp
  apply AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod.nativeChernForm_separating M.abelian C.ampleLine C.ample
  intro w
  change (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine (x - y)) w = 0
  rw [map_sub, LinearMap.sub_apply, h w, sub_self]

theorem PolarizationConstruction.ReferencePolarizationConstruction.latticeIsogeny_period_bijective :
    Function.Bijective (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (show M.abelian.toOver ⟶ N.abelian.toOver from p.isogeny.hom)) := by
  let f : M.abelian.toOver ⟶ N.abelian.toOver := p.isogeny.hom
  have hf := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ComplexFibers.NativeLinearMaps.rationalLift_injective_of_isFinite f
  have hd : Module.finrank ℚ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) =
      Module.finrank ℚ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods N.abelian) := by
    rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods_finrank, M.dimension, N.dimension]
  exact ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f).linearEquivOfInjective hf hd).bijective

end

end OAI.RepresentationTheory.Theta.Geometric.Reference
