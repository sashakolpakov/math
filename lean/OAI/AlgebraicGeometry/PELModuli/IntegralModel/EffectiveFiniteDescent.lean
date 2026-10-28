import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.Neighborhoods
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrbitQuotientExists
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Effective Finite Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.EffectiveFiniteDescent

noncomputable section

/-!
Effective finite descent for projective schemes from an actual overlap
relation. Invariant affine neighborhoods, their invariant-ring quotients,
and the glued quotient are constructed by the proved finite-relation
machinery. The square identifying the original scheme with the base change
of the constructed quotient is proved here by faithfully flat descent.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- Effectiveness of a quotient of a descent relation identifies the
quotient's base change with the original scheme. -/
theorem quotient_descent_square
    {B T R X Q : Scheme.{u}} (u : T ⟶ B) (a : X ⟶ T)
    (r : R ⟶ T) (s t : R ⟶ X)
    (hsource : IsPullback r s u (a ≫ u)) (ht : t ≫ a = r)
    (q : X ⟶ Q) [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (b : Q ⟶ B) (hqb : q ≫ b = a ≫ u) (hk : IsKernelPair q s t) :
    IsPullback a q u b := by
  let P := pullback u b
  let v : X ⟶ P := pullback.lift a q hqb.symm
  have hvfst : v ≫ pullback.fst u b = a := pullback.lift_fst _ _ _
  have hvsnd : v ≫ pullback.snd u b = q := pullback.lift_snd _ _ _
  have houter : IsPullback ((t ≫ v) ≫ pullback.fst u b) s u (q ≫ b) := by
    rw [Category.assoc, hvfst, ht, hqb]
    exact hsource
  have hcart : IsPullback (t ≫ v) s (pullback.snd u b) q :=
    houter.of_right (by rw [Category.assoc, hvsnd]; exact hk.w.symm)
      (.of_hasPullback u b)
  let XO : Over Q := Over.mk q
  let PO : Over Q := Over.mk (pullback.snd u b)
  let vO : XO ⟶ PO := Over.homMk v hvsnd
  let e : pullback q q ≅ pullback (pullback.snd u b) q :=
    hk.flip.isoPullback.symm ≪≫ hcart.isoPullback
  have he : ((Over.pullback q).map vO).left = e.hom := by
    apply pullback.hom_ext
    · have hl : ((Over.pullback q).map vO).left ≫ pullback.fst PO.hom q =
          pullback.fst XO.hom q ≫ vO.left := pullback.lift_fst _ _ _
      rw [hl]
      change pullback.fst q q ≫ v =
        (hk.flip.isoPullback.inv ≫ hcart.isoPullback.hom) ≫ pullback.fst (pullback.snd u b) q
      rw [Category.assoc, hcart.isoPullback_hom_fst,
        ← Category.assoc, hk.flip.isoPullback_inv_fst]
    · have hl : ((Over.pullback q).map vO).left ≫ pullback.snd PO.hom q =
          pullback.snd XO.hom q := pullback.lift_snd _ _ _
      rw [hl]
      change pullback.snd q q =
        (hk.flip.isoPullback.inv ≫ hcart.isoPullback.hom) ≫ pullback.snd (pullback.snd u b) q
      rw [Category.assoc, hcart.isoPullback_hom_snd,
        hk.flip.isoPullback_inv_snd]
  have hi : IsIso ((Over.pullback q).map vO).left := he ▸ e.isIso_hom
  have : IsIso v := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    (Specialization.base_change_square q vO).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hi
  exact IsPullback.of_iso_pullback ⟨hqb.symm⟩ (asIso v) hvfst hvsnd

/-- Construct the descended scheme by gluing invariant affine quotients.
Only the projective scheme and its ordinary overlap relation are input;
the quotient, its effectiveness, and the base-change identification are
all conclusions. -/
theorem effective_projective_finite_descent
    {K : Type u} [Field K] [Infinite K]
    {B T R X : Scheme.{u}} (u : T ⟶ B)
    [IsFinite u] [Flat u] [LocallyOfFinitePresentation u]
    (a : X ⟶ T) (r : R ⟶ T) (s t : R ⟶ X)
    (hsource : IsPullback r s u (a ≫ u)) (ht : t ≫ a = r)
    (relation : CategoryTheory.EquivalenceRelation s t)
    (n : ℕ) (i : X ⟶ ArithmeticGeometry.Models.SpreadingOut.Projective.Construction.ProjectiveConstruction.projectiveSpace (K := K) n)
    [IsClosedImmersion i] :
    ∃ (Q : Over B) (q : X ⟶ Q.left),
      IsPullback a q u Q.hom ∧
      IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
      IsKernelPair q s t ∧
      ∀ (Y : Scheme.{u}) (f : X ⟶ Y), s ≫ f = t ≫ f →
        ∃! g : Q.left ⟶ Y, q ≫ g = f := by
  have : IsFinite s := MorphismProperty.of_isPullback hsource inferInstance
  have ha : s ≫ (a ≫ u) = t ≫ (a ≫ u) := by
    rw [← hsource.w, ← ht, Category.assoc]
  have hOrbit : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related s t x y → y ∈ U := by
    intro x
    exact Projective.Neighborhoods.finite_set_affine_neighborhood_of_projective_embedding n i
      {y | Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related s t x y}
      (Quotients.FiniteDescent.Invariant.Construction.InvariantCore.finite_orbit s t x)
  obtain ⟨Q, q, hfin, hflat, hfp, hsurj, hk, hdesc⟩ :=
    Quotients.FiniteDescent.OrbitQuotientExists.Construction.OrbitQuotient.exists_quotient u (a ≫ u) r s t hsource relation ha hOrbit
  let := hflat
  let := hfp
  let := hsurj
  obtain ⟨b, hb, _⟩ := hdesc B (a ≫ u) ha
  exact ⟨Over.mk b, q, quotient_descent_square u a r s t hsource ht q b hb hk,
    hfin, hflat, hfp, hsurj, hk, hdesc⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.EffectiveFiniteDescent
