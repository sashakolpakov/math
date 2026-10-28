import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberHilbertFamily
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi

/-! # Fiber Hilbert Classifier -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberHilbertClassifier

noncomputable section

/-! A classifier of the actual fibers of a finite faithfully flat
cover is a monomorphism, and is closed when the target reference is proper. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {S : Scheme.{0}} {X Y H : Over S} (q : X ⟶ Y)
    [IsFinite q.left] [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (η : yoneda.obj H ⟶ HilbertScheme.Presentations.Hilbert.Functor.familyFunctor X) (u : Y ⟶ H)

theorem finiteFiberClassifier_mono [IsSeparated Y.hom]
    (hu : η.app (op Y) u = FiberHilbertFamily.finiteFiberHilbertFamily q) : Mono u := by
  constructor
  intro T h k he
  have nh := ConcreteCategory.congr_hom (η.naturality h.op) u
  have nk := ConcreteCategory.congr_hom (η.naturality k.op) u
  change η.app (op T) (h ≫ u) = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X h (η.app (op Y) u) at nh
  change η.app (op T) (k ≫ u) = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X k (η.app (op Y) u) at nk
  rw [hu] at nh nk
  have hf := nh.symm.trans ((congrArg (fun f => η.app (op T) f) he).trans nk)
  exact FiberHilbertFamily.fiberGraph_pullback_injective q T (congrArg Subtype.val hf)

theorem finiteFiberClassifier_closed [IsProper Y.hom] [IsSeparated H.hom]
    (hu : η.app (op Y) u = FiberHilbertFamily.finiteFiberHilbertFamily q) :
    IsClosedImmersion u.left := by
  have : Mono u := finiteFiberClassifier_mono q η u hu
  have : IsProper (u.left ≫ H.hom) := u.w.symm ▸ inferInstanceAs (IsProper Y.hom)
  have : IsProper u.left := IsProper.of_comp u.left H.hom
  have : LocallyQuasiFinite u.left :=
    AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.locallyQuasiFinite_of_formallyUnramified u.left
  have : IsFinite u.left := IsFinite.of_isProper_of_locallyQuasiFinite u.left
  exact (IsClosedImmersion.iff_isFinite_and_mono u.left).mpr ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberHilbertClassifier
