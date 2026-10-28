import OAI.RepresentationTheory.Theta.Geometric.Reference.PoincareDetection
import OAI.RepresentationTheory.Theta.Geometric.Reference.PELFamily
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli

/-! # Marked Chern Isometry -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Geometric.Reference

/-! An isometry of the original Chern period forms preserves the actual
reference polarizations. Its dual is the represented Picard dual, and
the resulting PEL isomorphism retains every ordered level equation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {M' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP} {N' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel G hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} {p' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M' N'}
    (C : PolarizationConstruction.ReferencePolarizationConstruction p) (C' : PolarizationConstruction.ReferencePolarizationConstruction p')
    (e : M.abelianScheme.scheme ≅ M'.abelianScheme.scheme) [IsMonHom e.hom]

def PolarizationConstruction.ReferencePolarizationConstruction.referenceDualIso : N.abelianScheme.scheme ≅ N'.abelianScheme.scheme :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnderlyingIso.dualFamilyIso C.dual C'.dual e

instance PolarizationConstruction.ReferencePolarizationConstruction.referenceDualIso_isMonHom : IsMonHom (C.referenceDualIso C' e).hom :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnderlyingIso.dualFamilyIso_isMonHom C.dual C'.dual e

theorem PolarizationConstruction.ReferencePolarizationConstruction.referenceDualIso_poincare :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((C.referenceDualIso C' e).hom ⊗ₘ e.hom).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C'.poincare) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C.poincare :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso.dualFamilyIso_poincare C.dual C'.dual e

theorem PolarizationConstruction.ReferencePolarizationConstruction.referenceDualIso_periodPairing (x : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods N.abelian) (y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    C'.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (C.referenceDualIso C' e).hom x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom y) =
      C.periodPairing x y := by
  have h := LinePeriodPairing.linePeriodPairing_pullback N.abelian M.abelian N'.abelian M'.abelian
    (C.referenceDualIso C' e).hom e.hom (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf C'.poincare) x y
  exact h.symm.trans (congrArg (fun q => LinePeriodPairing.linePeriodPairing N.abelian M.abelian q x y)
    (C.referenceDualIso_poincare C' e))

theorem PolarizationConstruction.ReferencePolarizationConstruction.polarizationIso_of_chern_isometry
    (he : ∀ x y, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M'.abelian C'.ampleLine (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom y) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y) :
    p.isogeny.hom ≫ (C.referenceDualIso C' e).hom = e.hom ≫ p'.isogeny.hom := by
  apply C'.periodPairing_detects_group_maps M.abelian
  intro x t
  obtain ⟨y, rfl⟩ := (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLiftIso (show M.abelian.toOver ≅ M'.abelian.toOver from e)).surjective t
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_comp]
  change C'.periodPairing
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (C.referenceDualIso C' e).hom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p.isogeny.hom x)) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom y) =
    C'.periodPairing (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift p'.isogeny.hom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom x)) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom y)
  rw [C.referenceDualIso_periodPairing C' e, C.periodPairing_isogeny, C'.periodPairing_isogeny]
  exact (he x y).symm

def PolarizationConstruction.ReferencePolarizationConstruction.pelFamilyIso_of_chern_isometry (level : ℕ) [NeZero level]
    (he : ∀ x y, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M'.abelian C'.ampleLine (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom y) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y)
    (ha : ∀ a : NumberField.RingOfIntegers E,
      M.integralAction.map a ≫ e.hom = e.hom ≫ M'.integralAction.map a)
    (hl : ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
      (c : LocallyConstant T.left (Multiplicative (Fin (2 * (3 * s)) → ZMod level))),
      ((M.fixedFullLevel level).hom.app (.op T) c).val ≫ e.hom =
        ((M'.fixedFullLevel level).hom.app (.op T) c).val) :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (C.pelFamily level) (C'.pelFamily level) where
  abelian := e
  dual := C.referenceDualIso C' e
  abelianGroup := inferInstance
  dualGroup := C.referenceDualIso_isMonHom C' e
  polarization := C.polarizationIso_of_chern_isometry C' e he
  poincare := C.referenceDualIso_poincare C' e
  equivariant := ha
  marking := hl

end RepresentationTheory.Theta.Geometric.Reference

namespace RepresentationTheory.Theta.Geometric.Reference.MarkedChernIsometry

/-! Exact reference markings transfer trace-form isometries to the
original algebraic Chern forms without changing the polarization. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {M' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP} {N' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel G hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} {p' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M' N'}

theorem reference_marked_chern_isometry
    (C : PolarizationConstruction.ReferencePolarizationConstruction p) (C' : PolarizationConstruction.ReferencePolarizationConstruction p')
    (f : M.abelian.toOver ⟶ M'.abelian.toOver) [IsMonHom f]
    (t : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E → NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (ht : ∀ u v, P.traceForm (t u) (t v) = P.traceForm u v)
    (hf : ∀ u, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f (M.nativeReferenceMarking u) = M'.nativeReferenceMarking (t u))
    (x y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M'.abelian C'.ampleLine (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y := by
  obtain ⟨u, rfl⟩ := M.nativeReferenceMarking.surjective x
  obtain ⟨v, rfl⟩ := M.nativeReferenceMarking.surjective y
  rw [hf, hf, C'.chern, C.chern, ht]

end RepresentationTheory.Theta.Geometric.Reference.MarkedChernIsometry

end

end OAI
