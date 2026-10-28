import OAI.RepresentationTheory.Theta.Geometric.Reference.DualMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods

/-! # Marked Chern Similitude -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Geometric.Reference

/-! Exact similitudes of the reference Chern form preserve the original
polarization morphism with its literal natural-number multiplier. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {M' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP} {N' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel G hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} {p' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M' N'}
    (C : PolarizationConstruction.ReferencePolarizationConstruction p) (C' : PolarizationConstruction.ReferencePolarizationConstruction p')
    (f : M.abelianScheme.scheme ⟶ M'.abelianScheme.scheme) [IsMonHom f]

theorem PolarizationConstruction.ReferencePolarizationConstruction.polarization_of_chern_similitude (n : ℕ)
    (hf : ∀ x y, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M'.abelian C'.ampleLine (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) =
      n • AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y) :
    f ≫ p'.isogeny.hom ≫ C.referenceDualMap C' f = p.isogeny.hom ^ n := by
  let : IsMonHom (p.isogeny.hom ^ n) :=
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps.nativePow_isMonHom (show M.abelian.toOver ⟶ N.abelian.toOver from p.isogeny.hom) n
  apply C.periodPairing_detects_group_maps M.abelian
  intro x y
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps.rationalLift_pow]
  change C.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (C.referenceDualMap C' f)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p'.isogeny.hom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x))) y =
      C.periodPairing (n • AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x) y
  rw [C.referenceDualMap_periodPairing C' f, C'.periodPairing_isogeny, map_nsmul,
    LinearMap.smul_apply, C.periodPairing_isogeny]
  exact hf x y

end RepresentationTheory.Theta.Geometric.Reference

namespace RepresentationTheory.Theta.Geometric.Reference.MarkedChernSimilitude

/-! Exact reference markings transfer scaled trace-form isometries to the
original algebraic Chern forms without changing the polarization. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {M' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP} {N' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel G hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} {p' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M' N'}

theorem reference_marked_chern_scaled_isometry
    (C : PolarizationConstruction.ReferencePolarizationConstruction p) (C' : PolarizationConstruction.ReferencePolarizationConstruction p')
    (f : M.abelian.toOver ⟶ M'.abelian.toOver) [IsMonHom f]
    (m : ℕ) (t : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (ht : ∀ u v, P.traceForm (t u) (t v) = P.traceForm u v)
    (hf : ∀ u, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f (M.nativeReferenceMarking u) = M'.nativeReferenceMarking (m • t u))
    (x y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M'.abelian C'.ampleLine (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) =
      (m * m) • AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y := by
  obtain ⟨u, rfl⟩ := M.nativeReferenceMarking.surjective x
  obtain ⟨v, rfl⟩ := M.nativeReferenceMarking.surjective y
  rw [hf, hf, map_nsmul, map_nsmul, map_nsmul, map_nsmul, LinearMap.smul_apply,
    smul_smul, C'.chern, C.chern, ht]

end RepresentationTheory.Theta.Geometric.Reference.MarkedChernSimilitude

end

end OAI
