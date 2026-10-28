import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FreeInvariant
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalSource

/-! # Orbit Quotient Exists -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrbitQuotientExists.Construction.OrbitQuotient

/-!
# Quotients from affine neighborhoods of finite subgroup orbits

All affine source bases and all invariant affine charts are constructed
locally. The only remaining geometric input is an affine neighborhood of
each orbit. No basis, invariant cover, transition map, or quotient is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem exists_quotient
    {H S R X : Scheme.{u}} (h : H ⟶ S) (a : X ⟶ S) (r : R ⟶ H) (s t : R ⟶ X)
    (hs : IsPullback r s h a) [IsFinite h] [Flat h] [LocallyOfFinitePresentation h]
    (e : CategoryTheory.EquivalenceRelation s t) (ha : s ≫ a = t ≫ a)
    (hOrbit : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ U) :
    ∃ (Q : Scheme.{u}) (π : X ⟶ Q),
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧ Surjective π ∧
      IsKernelPair π s t ∧
      ∀ (T : Scheme.{u}) (f : X ⟶ T), s ≫ f = t ≫ f →
        ∃! g : Q ⟶ T, π ≫ g = f := by
  have : IsFinite s := MorphismProperty.of_isPullback hs inferInstance
  apply FreeInvariant.Construction.FreeInvariantCover.exists_quotient_of_pointwise e
  intro x
  obtain ⟨B, hB, hxB, n, ⟨b⟩⟩ := SchemeTrivializationBasis.Construction.SchemeTrivialization.exists_basis_neighborhood h (a x)
  let : IsAffine B := hB
  obtain ⟨U, hU, hOU⟩ := hOrbit x
  have hOB : ∀ y, Invariant.Construction.InvariantCore.Related s t x y → y ∈ a ⁻¹ᵁ B := by
    rintro y ⟨z, hz, hz'⟩
    have he : a x = a y := by
      simpa only [Scheme.Hom.comp_apply, hz, hz'] using congrArg (fun f => f z) ha
    change a y ∈ B
    exact he ▸ hxB
  obtain ⟨D, hD, hOD, _, hDB⟩ := AffineNeighborhoodOpen.Construction.AffineNeighborhood.exists_affineOpen_subset X
    {y | Invariant.Construction.InvariantCore.Related s t x y} (Invariant.Construction.InvariantCore.finite_orbit s t x)
    U (a ⁻¹ᵁ B) hU hOU hOB
  obtain ⟨W, hW, hWD, hWi, hOW⟩ := InvariantAffineEq.Construction.InvariantAffine.exists_invariant_affine e x D hD
    (fun _ hy => hOD hy) (by
      intro E hE hED
      let : IsAffine E := hE
      exact ⟨n, LocalSource.Construction.LocalSourceBasis.exists_basis_over_open h a r s hs B E (hED.trans hDB) b⟩)
  let : IsAffine W := hW
  exact ⟨⟨W, hW, hWi, n,
    LocalSource.Construction.LocalSourceBasis.exists_basis_over_open h a r s hs B W (hWD.trans hDB) b⟩,
    hOW x (Invariant.Construction.InvariantCore.related_refl e x)⟩

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OrbitQuotientExists.Construction.OrbitQuotient
