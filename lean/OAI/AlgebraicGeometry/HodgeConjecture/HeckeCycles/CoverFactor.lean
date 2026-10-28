import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource

/-! # Cover Factor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM

noncomputable section

/-! Construct maps between actual ball quotients from inclusion of their
orbit relations. The map and its commuting equation follow from the
coverings; they are not additional family data. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable {D X Y : Type*}
  [TopologicalSpace D] [TopologicalSpace X] [TopologicalSpace Y]

def factor (π : D → X) (ρ : D → Y) (hπ : Function.Surjective π) : X → Y :=
  fun x => ρ (hπ x).choose

omit [TopologicalSpace D] [TopologicalSpace X] [TopologicalSpace Y] in
theorem factor_comp (π : D → X) (ρ : D → Y) (hπ : Function.Surjective π)
    (hfibers : ∀ z w, π z = π w → ρ z = ρ w) (z : D) :
    factor π ρ hπ (π z) = ρ z :=
  hfibers _ z (hπ (π z)).choose_spec

theorem factor_continuous (π : D → X) (ρ : D → Y)
    (hπ : Function.Surjective π) (hcover : IsCoveringMap π) (hρ : Continuous ρ)
    (hfibers : ∀ z w, π z = π w → ρ z = ρ w) :
    Continuous (factor π ρ hπ) := by
  apply (hcover.isQuotientMap hπ).continuous_iff.mpr
  convert hρ using 1
  funext z
  exact factor_comp π ρ hπ hfibers z

omit [TopologicalSpace D] [TopologicalSpace X] [TopologicalSpace Y] in
theorem factor_unique (π : D → X) (ρ : D → Y) (hπ : Function.Surjective π)
    (f : X → Y) (hf : ∀ z, f (π z) = ρ z) : f = factor π ρ hπ := by
  funext x
  calc
    f x = f (π (hπ x).choose) := congrArg f (hπ x).choose_spec.symm
    _ = ρ (hπ x).choose := hf _
    _ = factor π ρ hπ x := rfl

omit [TopologicalSpace D] [TopologicalSpace X] [TopologicalSpace Y] in
theorem factor_surjective (π : D → X) (ρ : D → Y)
    (hπ : Function.Surjective π) (hρ : Function.Surjective ρ)
    (hfibers : ∀ z w, π z = π w → ρ z = ρ w) :
    Function.Surjective (factor π ρ hπ) := by
  intro y
  obtain ⟨z, rfl⟩ := hρ y
  exact ⟨π z, factor_comp π ρ hπ hfibers z⟩

omit [TopologicalSpace D] [TopologicalSpace X] [TopologicalSpace Y] in
/-- A factor map is determined locally by either covering's actual local
sections. This equation is the input for proving its holomorphicity. -/
theorem factor_on_section (π : D → X) (ρ : D → Y) (hπ : Function.Surjective π)
    (hfibers : ∀ z w, π z = π w → ρ z = ρ w)
    (s : X → D) (U : Set X) (hs : ∀ x ∈ U, π (s x) = x) :
    Set.EqOn (factor π ρ hπ) (ρ ∘ s) U := by
  intro x hx
  calc
    factor π ρ hπ x = factor π ρ hπ (π (s x)) :=
      congrArg (factor π ρ hπ) (hs x hx).symm
    _ = ρ (s x) := factor_comp π ρ hπ hfibers (s x)

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]

/-- Preserve the actual Hermitian geometry while changing only its full
integral lattice, for comparison with the CongruenceLevel reference lattice. -/
def withLattice (B : GeometricSource.CM.BallDatum E) (Λ : Submodule ℤ (GeometricSource.CM.Vec E))
    (hfg : Λ.FG) (hfull : Submodule.span ℚ (Λ : Set (GeometricSource.CM.Vec E)) = ⊤)
    (hstable : ∀ (a : NumberField.RingOfIntegers E) (x : GeometricSource.CM.Vec E),
      x ∈ Λ → (a : E) • x ∈ Λ) : GeometricSource.CM.BallDatum E :=
  { B with lattice := Λ, lattice_fg := hfg, lattice_full := hfull, lattice_stable := hstable }

/-- Actual principal-level containment constructs the continuous
surjective map between the given quotients. -/
theorem map_of_principal_containment
    (B : GeometricSource.CM.BallDatum E) (Λ : Submodule ℤ (GeometricSource.CM.Vec E))
    (hfg : Λ.FG) (hfull : Submodule.span ℚ (Λ : Set (GeometricSource.CM.Vec E)) = ⊤)
    (hstable : ∀ (a : NumberField.RingOfIntegers E) (x : GeometricSource.CM.Vec E),
      x ∈ Λ → (a : E) • x ∈ Λ)
    (N L : ℕ) (X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : B.Domain → X.analyticSpace)
    (ρ : (withLattice E B Λ hfg hfull hstable).Domain → Y.analyticSpace)
    (hπ : B.IsBallCover L X π)
    (hρ : (withLattice E B Λ hfg hfull hstable).IsBallCover N Y ρ)
    (hcontain : ∀ g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E, B.principalLevel L g →
      (withLattice E B Λ hfg hfull hstable).principalLevel N g) :
    ∃ f : X.analyticSpace → Y.analyticSpace,
      Continuous f ∧ Function.Surjective f ∧ ∀ z : B.Domain, f (π z) = ρ z := by
  have hfibers : ∀ z w : B.Domain, π z = π w → ρ z = ρ w := by
    intro z w hzw
    obtain ⟨g, hg, hact⟩ := (hπ.2.2.2.2.2 z w).mp hzw
    exact (hρ.2.2.2.2.2 z w).mpr ⟨g, hcontain g hg, hact⟩
  exact ⟨factor π ρ hπ.2.1,
    factor_continuous π ρ hπ.2.1 hπ.2.2.1 hρ.2.2.1.continuous hfibers,
    factor_surjective π ρ hπ.2.1 hρ.2.1 hfibers,
    factor_comp π ρ hπ.2.1 hfibers⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM
