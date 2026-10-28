import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PurityConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ComplementNeighborhood

/-! # Pointed Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PointedPurity

noncomputable section

/-! Pointwise regular equations along the actual closed subscheme give
global concentration of its dual resolution. The complementary opens
are supplied by the closed immersion itself. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
  (j : σ) (B b : ℕ) (hb : b ≤ B) (c : ℕ)

include hb in
omit [LinearOrder σ] in
theorem exactAt
    (hpoint : ∀ x : X, ∃ (i : σ) (V : (Proj (homogeneousSubmodule σ R)).Opens)
      (_ : IsAffineOpen V), V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i ∧ f x ∈ V ∧
        ∃ rs : List Γ(Proj (homogeneousSubmodule σ R), V),
          RingHom.ker (f.app V).hom = Ideal.ofList rs ∧
            RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), V) rs ∧
              rs.length = c)
    (n : ℕ) (hn : n ≠ c) : (ClosedImmersionPurity.internalComplex f j B b).ExactAt n := by
  classical
  have hlocal (y : Proj (homogeneousSubmodule σ R)) :
      ∃ (V : (Proj (homogeneousSubmodule σ R)).Opens) (_ : IsAffineOpen V), y ∈ V ∧
        ∃ i : σ, V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i ∧
          (RingHom.ker (f.app V).hom = ⊤ ∨
            ∃ rs : List Γ(Proj (homogeneousSubmodule σ R), V),
              RingHom.ker (f.app V).hom = Ideal.ofList rs ∧
                RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), V) rs ∧
                  rs.length = c) := by
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨i, V, hV, hVi, hx, rs, hrs, hreg, hlen⟩ := hpoint x
      exact ⟨V, hV, hx, i, hVi, Or.inr ⟨rs, hrs, hreg, hlen⟩⟩
    · have hy' : y ∈ ⨆ i : σ, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i := by
        rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
        trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy'
      obtain ⟨V, hV, hVi, hyV, hunit⟩ :=
        Closed.ComplementNeighborhood.exists_affine f (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) y hi hy
      exact ⟨V, hV, hyV, i, hVi, Or.inl hunit⟩
  choose U hAffine hmem i hi heq using hlocal
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hmem y⟩
  exact PurityConcentration.exactAt_of_cover f j B b hb U hcover hAffine
    (fun a => ⟨i a, hi a⟩) c heq n hn

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PointedPurity
