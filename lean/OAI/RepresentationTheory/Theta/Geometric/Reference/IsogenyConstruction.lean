import OAI.RepresentationTheory.Theta.Geometric.Reference.MarkedChernSimilitude
import OAI.RepresentationTheory.Theta.Geometric.Reference.PELFamily
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Marking

/-! # Isogeny Construction -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference

noncomputable section

/-! Construct original marked PEL isogenies from an actual reference
isogeny and its proved Chern, action, and level equations. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}
    {M' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP} {N' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel G hP}
    {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} {p' : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M' N'}
    (C : PolarizationConstruction.ReferencePolarizationConstruction p) (C' : PolarizationConstruction.ReferencePolarizationConstruction p')

def PolarizationConstruction.ReferencePolarizationConstruction.pelIsogeny_of_chern_similitude (level : ℕ) [NeZero level] (a : (ZMod level)ˣ)
    (i : M.abelianScheme.Isogeny M'.abelianScheme) (n : ℕ)
    (he : ∀ x y, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M'.abelian C'.ampleLine (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift i.hom x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift i.hom y) =
      n • AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y)
    (ha : ∀ b : NumberField.RingOfIntegers E,
      M.integralAction.map b ≫ i.hom = i.hom ≫ M'.integralAction.map b)
    (hl : ∀ (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
      (c : LocallyConstant T.left (Multiplicative (Fin (2 * (3 * s)) → ZMod level))),
      ((C.pelFamily level).marking.hom.app (.op T) c).val ≫ i.hom =
        (((C'.pelFamily level).shiftMarking a).marking.hom.app (.op T) c).val) :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (C.pelFamily level) ((C'.pelFamily level).shiftMarking a) n where
  isogeny := i
  dualHom := C.referenceDualMap C' i.hom
  dualGroup := C.referenceDualMap_isMonHom C' i.hom
  poincare := (C.referenceDualMap_poincare C' i.hom).symm
  equivariant := ha
  polarization := C.polarization_of_chern_similitude C' i.hom n he
  marking := hl

end

end OAI.RepresentationTheory.Theta.Geometric.Reference
