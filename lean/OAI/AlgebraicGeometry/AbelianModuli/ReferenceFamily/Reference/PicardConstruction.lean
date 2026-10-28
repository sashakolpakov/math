import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AllTestPicardUniversality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.InfinitesimalPicardConstruction

/-! # Picard Construction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction

noncomputable section

/-! The marked theta construction supplies actual dual abelian data.
Its universal property is proved on all tests, rather than supplied as input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {z : P.domain}
    {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}

structure ReferencePicardConstruction (p : IsogenyKernel.ReferenceLatticeIsogeny M D) where
  ampleLine : HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left
  poincare : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left
  homogeneous : M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme
    (HilbertConstruction.Line.Bundles.LineBundle.classOf poincare)
  ample : ampleLine.IsAmple
  chern : ∀ u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Intrinsic.ChernPairing.nativeChernForm M.abelian ampleLine
    (M.nativeReferenceMarking u) (M.nativeReferenceMarking v) = P.traceForm u v
  universal : IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme poincare homogeneous)
  difference : (poincare.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
    (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme ampleLine).sheaf
  dualZero : (poincare.pullback (lift (1 : M.abelianScheme.scheme ⟶ D.abelianScheme.scheme)
    (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left
  abelianZero : (poincare.pullback (lift (𝟙 D.abelianScheme.scheme)
    (1 : D.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
      HilbertConstruction.Line.Bundles.structureModule D.abelianScheme.scheme.left

theorem referencePicardConstruction_nonempty (p : IsogenyKernel.ReferenceLatticeIsogeny M D) :
    Nonempty (ReferencePicardConstruction p) := by
  obtain ⟨L, Q, hQ, hamp, hchern, hinj, _, hcomplex, ⟨recover⟩, ⟨eD⟩, ⟨eA⟩, _⟩ :=
    p.exists_normalized_infinitesimal_picard_classification
  exact ⟨⟨L, Q, hQ, hamp, hchern,
    M.referenceHomogeneousParameterMap_isIso D Q eA hinj hQ hcomplex.surjective, recover, eD, eA⟩⟩

namespace ReferencePicardConstruction

variable {p : IsogenyKernel.ReferenceLatticeIsogeny M D} (C : ReferencePicardConstruction p)

def dual : HilbertConstruction.Dual.Data.DualAbelianData M.abelianScheme :=
  letI := C.universal
  RepresentationTheory.Theta.Geometric.Dual.PicardData.dualDataOfHomogeneousParameterIso M.abelianScheme D.abelianScheme C.poincare C.homogeneous
    C.abelianZero C.dualZero

theorem dual_abelian : C.dual.abelian = D.abelianScheme := rfl

theorem dual_poincare : C.dual.poincare = C.poincare := rfl

theorem dual_parameter {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (a : T ⟶ D.abelianScheme.scheme) :
    C.dual.representable.homEquiv a = RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass M.abelianScheme C.poincare C.homogeneous a :=
  rfl

end ReferencePicardConstruction

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardConstruction
