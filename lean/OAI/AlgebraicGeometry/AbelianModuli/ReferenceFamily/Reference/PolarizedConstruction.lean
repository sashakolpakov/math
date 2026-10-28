import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyType
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelComparison
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PositiveDifference

/-! # Polarized Construction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The constructed universal Poincare bundle gives the original
reference lattice isogeny an actual polarization and ordered full levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PositiveDifference

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {z : P.domain}
    {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    {p : IsogenyKernel.ReferenceLatticeIsogeny M D} (C : PicardConstruction.ReferencePicardConstruction p)

def PicardConstruction.ReferencePicardConstruction.polarization : HilbertConstruction.PolarizationData.Polarization C.dual P.polarizationType where
  isogeny := p.isogeny
  kernelType := p.hasPolarizationType
  positive K _ _ k := RepresentationTheory.Theta.Geometric.Intrinsic.PositiveDifference.positiveOnGeometricFiber_of_difference_iso C.dual p.isogeny C.ampleLine
    C.ample C.difference K k

def PicardConstruction.ReferencePicardConstruction.polarized (N : ℕ) [NeZero N] :
    HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N Foundations.Scheme.ProjectiveSpace.complexBase where
  abelian := M.abelianScheme
  dual := C.dual
  polarization := C.polarization
  level := M.fixedFullLevel N

theorem PicardConstruction.ReferencePicardConstruction.polarized_level_reference (N : ℕ) [NeZero N] (v : P.lattice) :
    ((((C.polarized N).level).hom.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)))
      (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd (P.fixedLevelLabel hP N v)))).val =
        M.period (F.divisionPoint N v) :=
  M.fixedFullLevel_reference N v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
