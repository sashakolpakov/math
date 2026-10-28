import OAI.RepresentationTheory.Theta.Geometric.Reference.RelativePicard
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyType
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PositiveDifference

/-! # Polarization Construction -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.PolarizationConstruction

noncomputable section

/-! The reference theta construction supplies actual normalized dual data
and a polarization with the original lattice isogeny and ordered levels. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FixedBasis

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel F hP}

structure ReferencePolarizationConstruction (p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N) where
  ampleLine : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left
  poincare : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left
  homogeneous : M.abelianScheme.IsHomogeneousPicardClass N.abelianScheme.scheme
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf poincare)
  ample : ampleLine.IsAmple
  chern : ∀ u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm M.abelian ampleLine
    (M.nativeReferenceMarking u) (M.nativeReferenceMarking v) = P.traceForm u v
  universal : IsIso (ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme poincare homogeneous)
  difference : (poincare.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
    (AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme ampleLine).sheaf
  dualZero : (poincare.pullback (lift (1 : M.abelianScheme.scheme ⟶ N.abelianScheme.scheme)
    (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left
  abelianZero : (poincare.pullback (lift (𝟙 N.abelianScheme.scheme)
    (1 : N.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule N.abelianScheme.scheme.left

theorem referencePolarizationConstruction_nonempty (p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N) :
    Nonempty (ReferencePolarizationConstruction p) := by
  obtain ⟨L, Q, hQ, hL, hchern, hiso, ⟨ed⟩, ⟨en⟩, ⟨ea⟩⟩ :=
    RelativePicard.exists_reference_relative_picard_classification p
  exact ⟨⟨L, Q, hQ, hL, hchern, hiso, ed, en, ea⟩⟩

namespace ReferencePolarizationConstruction

variable {p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny M N} (C : ReferencePolarizationConstruction p)

def dual : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData M.abelianScheme :=
  letI := C.universal
  Dual.PicardData.dualDataOfHomogeneousParameterIso M.abelianScheme N.abelianScheme C.poincare C.homogeneous
    C.abelianZero C.dualZero

def polarization : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.Polarization C.dual P.polarizationType where
  isogeny := p.isogeny
  kernelType := p.hasPolarizationType
  positive K _ _ k := Intrinsic.PositiveDifference.positiveOnGeometricFiber_of_difference_iso C.dual p.isogeny C.ampleLine
    C.ample C.difference K k

def polarized (level : ℕ) [NeZero level] :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType level AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase where
  abelian := M.abelianScheme
  dual := C.dual
  polarization := C.polarization
  level := M.fixedFullLevel level

theorem polarized_level_reference (level : ℕ) [NeZero level] (v : P.lattice) :
    ((((C.polarized level).level).hom.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
      (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase (Multiplicative.ofAdd (P.fixedLevelLabel hP level v)))).val =
        M.period (F.divisionPoint level v) :=
  M.fixedFullLevel_reference level v

end ReferencePolarizationConstruction

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.PolarizationConstruction
