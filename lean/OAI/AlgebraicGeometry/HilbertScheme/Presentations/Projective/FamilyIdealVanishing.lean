import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AmbientContainmentLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WholeFamily

/-! # Family Ideal Vanishing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FamilyIdealVanishing.Core

noncomputable section

/-! Vanishing of an arbitrary ambient ideal on a flat proper
projective source is represented by an actual closed parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X B : Over S} [IsLocallyNoetherian B.left]
variable [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]

theorem projective_family_ideal_vanishing_closed_locus (BX : Has.Core.ProjectivePresentation X)
    (K : (Hilbert.Functor.ambient X B).IdealSheafData) :
    ∃ (Z : Over S) (j : Z ⟶ B), IsClosedImmersion j.left ∧
      (∀ (T : Over S) (x : T ⟶ B), K.comap (Hilbert.Functor.ambientMap X x) = ⊥ ↔
        ∃! y : T ⟶ Z, y ≫ j = x) ∧
      ∃ e : yoneda.obj Z ≅ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X K ⊥).toFunctor,
        e.hom ≫ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X K ⊥).ι = yoneda.map j := by
  obtain ⟨Z, j, hj, htest, he⟩ := AmbientContainmentLocus.Core.projective_ambient_containment_closed_locus BX (WholeFamily.Hilbert.wholeFamily X B) K
  refine ⟨Z, j, hj, ?_, he⟩
  intro T x
  have h := htest T x
  rw [WholeFamily.Hilbert.wholeFamily_pullback] at h
  change K.comap (Hilbert.Functor.ambientMap X x) ≤ ⊥ ↔ _ at h
  rwa [le_bot_iff] at h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FamilyIdealVanishing.Core
