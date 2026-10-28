import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentGlobalRepresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientIdealNaturality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.AmbientProjectivePresentation

/-! # Ambient Containment Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AmbientContainmentLocus.Core

noncomputable section

/-! An arbitrary chosen projective ambient embedding reduces native
ideal containment to polynomial projective space, giving a global
closed representing locus on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X B : Over S} [IsLocallyNoetherian B.left]

theorem projective_ambient_containment_closed_locus (BX : Has.Core.ProjectivePresentation X)
    (F : Hilbert.Functor.Family X B) (K : (Hilbert.Functor.ambient X B).IdealSheafData) :
    ∃ (Z : Over S) (j : Z ⟶ B), IsClosedImmersion j.left ∧
      (∀ (T : Over S) (x : T ⟶ B), K.comap (Hilbert.Functor.ambientMap X x) ≤
        (Hilbert.Functor.pullbackFamily X x F).val ↔ ∃! y : T ⟶ Z, y ≫ j = x) ∧
      ∃ e : yoneda.obj Z ≅ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X K F.val).toFunctor,
        e.hom ≫ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X K F.val).ι = yoneda.map j := by
  let i := BX.closedAmbientEmbedding
  let G := Hilbert.ClosedAmbientMap.pushforwardFamily i F
  let L := K.map (Hilbert.ClosedAmbientMap.ambientEmbedding i B)
  obtain ⟨Z, j, hj, htest, he⟩ := Intrinsic.ContainmentGlobalRepresentation.GradedHilbert.native_projective_containment_closed_locus B BX.dimension G L
  refine ⟨Z, j, hj, ?_, ?_⟩
  · intro T x
    exact (Closed.AmbientIdealNaturality.Hilbert.idealContainmentParameter_pushforward_iff i K F.val x).trans (htest T x)
  · have hEq : Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor
        (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S BX.dimension) L G.val =
        Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X K F.val :=
      Closed.AmbientIdealNaturality.Hilbert.idealContainmentParameter_pushforward_eq i K F.val
    rwa [hEq] at he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AmbientContainmentLocus.Core
