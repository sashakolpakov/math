import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberHilbertClassifier
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.HilbertRepresentation

/-! # Fiber Projective Classifier -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberProjectiveClassifier

noncomputable section

/-! A finite faithfully flat cover with a fixed actual fiber Hilbert
polynomial embeds its proper target into the constructed projective
Hilbert parameter. The classifier is recovered from representability. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

theorem finite_cover_target_projective_of_fiber_polynomial
    {S : Scheme.{0}} [IsLocallyNoetherian S] {X Y : Over S}
    (q : X ⟶ Y) [IsFinite q.left] [Flat q.left] [Surjective q.left]
    [LocallyOfFinitePresentation q.left] [IsProper Y.hom]
    (BX : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) (P : Polynomial ℚ)
    (hP : HilbertScheme.Presentations.Has.Core.HasFiberHilbertPolynomial BX (FiberHilbertFamily.finiteFiberHilbertFamily q) P) :
    HilbertScheme.Presentations.Has.Core.IsProjectiveOver Y := by
  obtain ⟨H, ⟨BH⟩, ⟨e⟩⟩ := Projective.HilbertRepresentation.projective_hilbert_representation BX P
  let F : (HilbertScheme.Presentations.Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor BX P).toFunctor.obj (op Y) :=
    ⟨FiberHilbertFamily.finiteFiberHilbertFamily q, hP⟩
  let u : Y ⟶ H := e.inv.app (op Y) F
  let η : yoneda.obj H ⟶ HilbertScheme.Presentations.Hilbert.Functor.familyFunctor X :=
    e.hom ≫ (HilbertScheme.Presentations.Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor BX P).ι
  have hu : η.app (op Y) u = FiberHilbertFamily.finiteFiberHilbertFamily q := by
    change (e.hom.app (op Y) (e.inv.app (op Y) F)).val = _
    have h := ConcreteCategory.congr_hom (e.inv_hom_id_app (op Y)) F
    change e.hom.app (op Y) (e.inv.app (op Y) F) = F at h
    exact congrArg (fun z : (HilbertScheme.Presentations.Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor BX P).toFunctor.obj (op Y) => z.val) h
  have : IsProper H.hom := BH.proper
  have : IsClosedImmersion u.left := FiberHilbertClassifier.finiteFiberClassifier_closed q η u hu
  exact ⟨BH.precompose u⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.FiberProjectiveClassifier
