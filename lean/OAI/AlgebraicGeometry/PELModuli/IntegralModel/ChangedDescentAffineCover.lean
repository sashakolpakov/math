import OAI.AlgebraicGeometry.PELModuli.IntegralModel.BaseChangedKernelPair
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.OrbitEffectiveDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.QuotientAffineCover

/-! # Changed Descent Affine Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChangedDescentAffineCover

noncomputable section

section

/-! Affine neighborhoods on a base-changed family give a finite invariant
affine cover for its actual base-changed descent relation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem baseChanged_descent_finite_invariant_affine_cover
    {S S' : Scheme.{0}} (b : S' ⟶ S) {B T R X : Over S}
    (u : T ⟶ B) [IsFinite u.left] [Flat u.left] [LocallyOfFinitePresentation u.left]
    (a : X ⟶ T) (r : R ⟶ T) (s t : R ⟶ X)
    (hsource : IsPullback r s u (a ≫ u)) (ht : t ≫ a = r)
    (e : CategoryTheory.EquivalenceRelation s t)
    [CompactSpace ((Over.pullback b).obj X).left]
    (hAF : ∀ F : Set ((Over.pullback b).obj X).left, F.Finite →
      ∃ V : ((Over.pullback b).obj X).left.Opens, IsAffineOpen V ∧ F ⊆ V) :
    ∃ (I : Type) (_ : Finite I) (V : I → ((Over.pullback b).obj X).left.Opens),
      (∀ i, IsAffineOpen (V i)) ∧
      (∀ i, ((Over.pullback b).map s).left ⁻¹ᵁ V i =
        ((Over.pullback b).map t).left ⁻¹ᵁ V i) ∧ iSup V = ⊤ := by
  let F := Over.pullback b
  let u' := (F.map u).left
  let a' := (F.map a).left
  let r' := (F.map r).left
  let s' := (F.map s).left
  let t' := (F.map t).left
  have : IsFinite u' := MorphismProperty.of_isPullback (Specialization.base_change_square b u)
    (inferInstanceAs (IsFinite u.left))
  have : Flat u' := MorphismProperty.of_isPullback (Specialization.base_change_square b u)
    (inferInstanceAs (Flat u.left))
  have : LocallyOfFinitePresentation u' := MorphismProperty.of_isPullback (Specialization.base_change_square b u)
    (inferInstanceAs (LocallyOfFinitePresentation u.left))
  have hc : IsPullback r' s' u' (a' ≫ u') := by
    have h := (hsource.map F).map (Over.forget S')
    change IsPullback r' s' u' (F.map (a ≫ u)).left at h
    rw [F.map_comp, Over.comp_left] at h
    exact h
  have ht' : t' ≫ a' = r' := by
    have h := congrArg (fun q => (F.map q).left) ht
    simpa only [F.map_comp, Over.comp_left] using h
  let e' := AbelianModuli.ReferenceFamily.RepresentedRelations.over_equivalenceRelation_left (BaseChangedKernelPair.overPullback_equivalenceRelation b e)
  have : IsFinite s' := MorphismProperty.of_isPullback hc (inferInstanceAs (IsFinite u'))
  have hOrbit : ∀ x : ((Over.pullback b).obj X).left,
      ∃ V : ((Over.pullback b).obj X).left.Opens, IsAffineOpen V ∧
        ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related s' t' x y → y ∈ V := by
    intro x
    exact hAF _ (Quotients.FiniteDescent.Invariant.Construction.InvariantCore.finite_orbit s' t' x)
  obtain ⟨Q, q, _, hf, _, _, _, hk, _⟩ :=
    Affine.OrbitEffectiveDescent.effective_finite_descent_from_affine_orbits u' a' r' s' t' hc ht' e' hOrbit
  have : IsFinite q := hf
  exact IntegralModel.Finite.QuotientAffineCover.finite_invariant_affine_cover_of_finite_map q s' t' hk.w

end

/-! Effective smooth proper family descent on a scalar-changed diagram
from its actual invariant affine cover. The source, relation, and quotient
base all remain the literal base changes of the original diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem baseChanged_effective_descent_of_invariant_cover
    {S S' : Scheme.{0}} (b : S' ⟶ S) {B T R X : Over S}
    (u : T ⟶ B) [IsFinite u.left] [Flat u.left] [Surjective u.left] [LocallyOfFinitePresentation u.left]
    (a : X ⟶ T) [Smooth a.left] [IsProper a.left] [GeometricallyConnected a.left]
    (r : R ⟶ T) (s t : R ⟶ X)
    (hsource : IsPullback r s u (a ≫ u)) (ht : t ≫ a = r)
    (e : CategoryTheory.EquivalenceRelation s t)
    {I : Type} (V : I → ((Over.pullback b).obj X).left.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcover : iSup V = ⊤)
    (hInv : ∀ i, ((Over.pullback b).map s).left ⁻¹ᵁ V i = ((Over.pullback b).map t).left ⁻¹ᵁ V i) :
    ∃ (A : Over ((Over.pullback b).obj B).left) (q : ((Over.pullback b).obj X).left ⟶ A.left),
      IsPullback ((Over.pullback b).map a).left q ((Over.pullback b).map u).left A.hom ∧
      Smooth A.hom ∧ IsProper A.hom ∧ GeometricallyConnected A.hom ∧
      IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
      IsKernelPair q ((Over.pullback b).map s).left ((Over.pullback b).map t).left := by
  let F := Over.pullback b
  let u' := (F.map u).left
  let a' := (F.map a).left
  let r' := (F.map r).left
  let s' := (F.map s).left
  let t' := (F.map t).left
  have : IsFinite u' := MorphismProperty.of_isPullback (Specialization.base_change_square b u)
    (inferInstanceAs (IsFinite u.left))
  have : Flat u' := MorphismProperty.of_isPullback (Specialization.base_change_square b u)
    (inferInstanceAs (Flat u.left))
  have : Surjective u' := MorphismProperty.of_isPullback (Specialization.base_change_square b u)
    (inferInstanceAs (Surjective u.left))
  have : LocallyOfFinitePresentation u' := MorphismProperty.of_isPullback (Specialization.base_change_square b u)
    (inferInstanceAs (LocallyOfFinitePresentation u.left))
  have : Smooth a' := MorphismProperty.of_isPullback (Specialization.base_change_square b a)
    (inferInstanceAs (Smooth a.left))
  have : IsProper a' := MorphismProperty.of_isPullback (Specialization.base_change_square b a)
    (inferInstanceAs (IsProper a.left))
  have : GeometricallyConnected a' := MorphismProperty.of_isPullback (Specialization.base_change_square b a)
    (inferInstanceAs (GeometricallyConnected a.left))
  have hc : IsPullback r' s' u' (a' ≫ u') := by
    have h := (hsource.map F).map (Over.forget S')
    change IsPullback r' s' u' (F.map (a ≫ u)).left at h
    rw [F.map_comp, Over.comp_left] at h
    exact h
  have ht' : t' ≫ a' = r' := by
    have h := congrArg (fun q => (F.map q).left) ht
    simpa only [F.map_comp, Over.comp_left] using h
  exact Affine.OrbitEffectiveDescent.effective_smooth_proper_descent_from_affine_orbits u' a' r' s' t' hc ht'
    (AbelianModuli.ReferenceFamily.RepresentedRelations.over_equivalenceRelation_left (BaseChangedKernelPair.overPullback_equivalenceRelation b e))
    (IntegralModel.Finite.QuotientAffineCover.affine_orbits_of_invariant_cover s' t' V hV hInv hcover)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChangedDescentAffineCover
