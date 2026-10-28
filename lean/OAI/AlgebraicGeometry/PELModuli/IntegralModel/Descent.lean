import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EffectiveFiniteDescent
import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Descent

noncomputable section

/-! Smoothness, properness, and geometric connectedness of the constructed
finite descent model. These properties are proved by faithfully flat base
change and do not occur as fields in the descended scheme's definition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- Scheme diagonals are immersions, so universal closedness of the
diagonal is equivalent to separatedness. -/
theorem separated_iff_diagonal_universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSeparated f ↔
      (MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme.{u})) f := by
  refine Iff.trans ?_ (MorphismProperty.diagonal_iff
    (P := (@UniversallyClosed : MorphismProperty Scheme.{u}))).symm
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let : UniversallyClosed (pullback.diagonal f) := h
    exact ⟨IsClosedImmersion.of_isPreimmersion _
      (pullback.diagonal f).isClosedMap.isClosed_range⟩

theorem proper_of_faithfully_flat_cartesian
    {W X T B : Scheme.{u}} {p : W ⟶ T} {q : W ⟶ X} {u : T ⟶ B} {f : X ⟶ B}
    (h : IsPullback p q u f) [Flat u] [Surjective u] [QuasiCompact u]
    [IsProper p] : IsProper f := by
  have hu : ((@Surjective ⊓ @Flat ⊓ @QuasiCompact) : MorphismProperty Scheme.{u}) u :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let UC : MorphismProperty Scheme.{u} := @UniversallyClosed
  let FC : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have : UC.DescendsAlong FC := inferInstanceAs
    (MorphismProperty.DescendsAlong (@UniversallyClosed : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact))
  have : UC.RespectsIso := universallyClosed_respectsIso
  have : FC.IsStableUnderBaseChange := ⟨fun h hf ↦
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h hf.1.1,
       MorphismProperty.of_isPullback (P := @Flat) h hf.1.2⟩,
      MorphismProperty.of_isPullback (P := @QuasiCompact) h hf.2⟩⟩
  have hdiag :
      (MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme.{u})) f :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := UC.diagonal) (Q := FC) h hu
      ((separated_iff_diagonal_universallyClosed p).mp inferInstance)
  have : IsSeparated f := (separated_iff_diagonal_universallyClosed f).mpr hdiag
  have : UniversallyClosed f := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h hu inferInstance
  have : LocallyOfFiniteType f := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @LocallyOfFiniteType) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h hu inferInstance
  exact ⟨⟩

/-- A smooth proper geometrically connected projective object with a
finite faithfully flat descent relation has a constructed smooth proper
geometrically connected model and its actual base-change identification. -/
theorem effective_smooth_proper_connected_descent
    {K : Type u} [Field K] [Infinite K]
    {B T R X : Scheme.{u}} (u : T ⟶ B)
    [IsFinite u] [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    (a : X ⟶ T) [Smooth a] [IsProper a] [GeometricallyConnected a]
    (r : R ⟶ T) (s t : R ⟶ X)
    (hsource : IsPullback r s u (a ≫ u)) (ht : t ≫ a = r)
    (relation : CategoryTheory.EquivalenceRelation s t)
    (n : ℕ) (i : X ⟶ ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveSpace (K := K) n)
    [IsClosedImmersion i] :
    ∃ (Q : Over B) (q : X ⟶ Q.left),
      IsPullback a q u Q.hom ∧
      Smooth Q.hom ∧ IsProper Q.hom ∧ GeometricallyConnected Q.hom ∧
      IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
      IsKernelPair q s t := by
  obtain ⟨Q, q, hcart, hfin, hflat, hfp, hsurj, hk, _⟩ :=
    EffectiveFiniteDescent.effective_projective_finite_descent u a r s t hsource ht relation n i
  have hs : Smooth Q.hom := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hcart
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hp : IsProper Q.hom := proper_of_faithfully_flat_cartesian hcart
  have hc : GeometricallyConnected Q.hom :=
    ArithmeticGeometry.Models.SpreadingOut.GeometricDescent.Construction.geometricallyConnected_of_surjective_cartesian hcart.flip
  exact ⟨Q, q, hcart, hs, hp, hc, hfin, hflat, hfp, hsurj, hk⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Descent
