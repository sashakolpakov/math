import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Descent

/-! # Orbit Effective Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.OrbitEffectiveDescent

noncomputable section

/-! Effective finite scheme descent from actual affine orbit
neighborhoods, with smooth proper connected geometry descended through
the constructed Cartesian square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem effective_finite_descent_from_affine_orbits
    {B T R X : Scheme.{0}} (u : T ⟶ B)
    [IsFinite u] [Flat u] [LocallyOfFinitePresentation u]
    (a : X ⟶ T) (r : R ⟶ T) (s t : R ⟶ X)
    (hsource : IsPullback r s u (a ≫ u)) (ht : t ≫ a = r)
    (relation : CategoryTheory.EquivalenceRelation s t)
    (hOrbit : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧
      ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related s t x y → y ∈ V) :
    ∃ (Q : Over B) (q : X ⟶ Q.left),
      IsPullback a q u Q.hom ∧
      IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
      IsKernelPair q s t ∧
      ∀ (Y : Scheme.{0}) (f : X ⟶ Y), s ≫ f = t ≫ f →
        ∃! g : Q.left ⟶ Y, q ≫ g = f := by
  have ha : s ≫ (a ≫ u) = t ≫ (a ≫ u) := by
    rw [← hsource.w, ← ht, Category.assoc]
  obtain ⟨Q, q, hfin, hflat, hfp, hsurj, hk, hdesc⟩ :=
    Quotients.FiniteDescent.OrbitQuotientExists.Construction.OrbitQuotient.exists_quotient u (a ≫ u) r s t hsource relation ha hOrbit
  have : Flat q := hflat
  have : LocallyOfFinitePresentation q := hfp
  have : Surjective q := hsurj
  obtain ⟨b, hb, _⟩ := hdesc B (a ≫ u) ha
  exact ⟨Over.mk b, q, EffectiveFiniteDescent.quotient_descent_square u a r s t hsource ht q b hb hk,
    hfin, hflat, hfp, hsurj, hk, hdesc⟩

theorem effective_smooth_proper_descent_from_affine_orbits
    {B T R X : Scheme.{0}} (u : T ⟶ B)
    [IsFinite u] [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    (a : X ⟶ T) [Smooth a] [IsProper a] [GeometricallyConnected a]
    (r : R ⟶ T) (s t : R ⟶ X)
    (hsource : IsPullback r s u (a ≫ u)) (ht : t ≫ a = r)
    (relation : CategoryTheory.EquivalenceRelation s t)
    (hOrbit : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧
      ∀ y, Quotients.FiniteDescent.Invariant.Construction.InvariantCore.Related s t x y → y ∈ V) :
    ∃ (Q : Over B) (q : X ⟶ Q.left),
      IsPullback a q u Q.hom ∧
      Smooth Q.hom ∧ IsProper Q.hom ∧ GeometricallyConnected Q.hom ∧
      IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
      IsKernelPair q s t := by
  obtain ⟨Q, q, hcart, hfin, hflat, hfp, hsurj, hk, _⟩ :=
    effective_finite_descent_from_affine_orbits u a r s t hsource ht relation hOrbit
  have hs : Smooth Q.hom := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hcart
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  exact ⟨Q, q, hcart, hs, Descent.proper_of_faithfully_flat_cartesian hcart,
    ArithmeticGeometry.Models.SpreadingOut.GeometricDescent.Construction.geometricallyConnected_of_surjective_cartesian hcart.flip,
    hfin, hflat, hfp, hsurj, hk⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.OrbitEffectiveDescent
