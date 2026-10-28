import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Scheme
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctor

/-! # Has -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Has

noncomputable section

/-! The actual polarization kernel scheme and its monomorphism into
the group scheme, with the universal property for all test schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

def polarizationKernel : Over A.left := by
  haveI := Scheme.Construction.polarizationKernelSchemeSubfunctor_isRepresentable A L
  exact RepresentedSubfunctor.Construction.representedSubfunctorFamily (Scheme.Construction.polarizationKernelSchemeSubfunctor A L)

instance polarizationKernel_mono : Mono (polarizationKernel A L).hom := by
  have := Scheme.Construction.polarizationKernelSchemeSubfunctor_isRepresentable A L
  exact RepresentedSubfunctor.Construction.representedSubfunctorFamily_mono (Scheme.Construction.polarizationKernelSchemeSubfunctor A L)

theorem polarizationKernel_hasLift_iff {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A) :
    Nonempty (Over.mk a.left ⟶ polarizationKernel A L) ↔
      Polarization.PicardMap.Construction.polarizationRelativeSection A L a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  have := Scheme.Construction.polarizationKernelSchemeSubfunctor_isRepresentable A L
  have hp := OverSubfunctor.Construction.overSubfunctor_mem (Functor.Construction.polarizationKernelSubfunctor A L) a
  have hf := RepresentedSubfunctor.Construction.representedSubfunctor_factorization (Scheme.Construction.polarizationKernelSchemeSubfunctor A L) T.left a.left
  constructor
  · rintro ⟨v⟩
    exact hp.mp (hf.mpr ⟨v.left, v.w⟩)
  · intro h
    obtain ⟨v, hv⟩ := hf.mp (hp.mpr h)
    exact ⟨Over.homMk v hv⟩

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Has
