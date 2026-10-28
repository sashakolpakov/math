import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ClosedImmersionPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomCoherence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalExactness

/-! # Purity Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PurityConcentration

noncomputable section

/-! Regular defining equations of fixed length concentrate the actual
dual resolution in that degree. Opens disjoint from the closed image
contribute zero cohomology in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
open scoped Pointwise

set_option backward.isDefEq.respectTransparency false

universe u v

theorem unit_regular (A : Type u) [CommRing A] :
    RingTheory.Sequence.IsWeaklyRegular A ([1] : List A) := by
  apply (RingTheory.Sequence.isWeaklyRegular_singleton_iff A 1).mpr
  intro x y h
  simpa only [one_smul] using h

theorem unit_quotient_zero (A : Type u) [CommRing A] :
    IsZero (ProjectiveResolution.DualPurity.quotient A ([1] : List A)) := by
  change IsZero (ModuleCat.of A (A ⧸ (Ideal.ofList ([1] : List A) • (⊤ : Submodule A A))))
  have he : Ideal.ofList ([1] : List A) • (⊤ : Submodule A A) = ⊤ := by simp
  rw [he]
  exact ModuleCat.isZero_of_subsingleton _

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ClosedImmersionPurity

variable {X : Scheme.{u}} (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
  (j : σ) (B b : ℕ)

omit [LinearOrder σ] in
theorem exactAt_of_unit (U : (Proj (homogeneousSubmodule σ R)).Opens) (hU : IsAffineOpen U)
    (i : σ) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (hunit : RingHom.ker (f.app U).hom = ⊤) (n : ℕ) :
    (ClosedImmersionPurity.sectionComplex f j B b U).ExactAt n := by
  let rs : List Γ(Proj (homogeneousSubmodule σ R), U) := [1]
  have hrs : RingHom.ker (f.app U).hom = Ideal.ofList rs := by simpa [rs] using hunit
  by_cases hn : n = rs.length
  · subst n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    apply (ClosedImmersionPurity.purityIso f j B b U hU i hUi rs (unit_regular _) hrs).isZero_iff.mpr
    exact (forget₂ (ModuleCat Γ(Proj (homogeneousSubmodule σ R), U)) AddCommGrpCat).map_isZero
      (unit_quotient_zero _)
  · exact ClosedImmersionPurity.exactAt f j B b U hU i hUi rs (unit_regular _) hrs n hn

omit [LinearOrder σ] in
theorem exactAt_of_cover (hb : b ≤ B) {τ : Type v}
    (U : τ → (Proj (homogeneousSubmodule σ R)).Opens) (hcover : iSup U = ⊤)
    (haffine : ∀ a, IsAffineOpen (U a))
    (hcoordinate : ∀ a, ∃ i : σ, U a ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (c : ℕ)
    (hlocal : ∀ a, RingHom.ker (f.app (U a)).hom = ⊤ ∨
      ∃ rs : List Γ(Proj (homogeneousSubmodule σ R), U a),
        RingHom.ker (f.app (U a)).hom = Ideal.ofList rs ∧
          RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), U a) rs ∧
            rs.length = c) (n : ℕ) (hn : n ≠ c) :
    (ClosedImmersionPurity.internalComplex f j B b).ExactAt n := by
  let (q : ℕ) : ((ClosedImmersionPurity.internalComplex f j B b).X q).IsQuasicoherent :=
    InternalHomCoherence.term (ClosedImmersionPurity.directImage f) j B b hb q
  apply Affine.LocalExactness.exactAt_of_cover (ClosedImmersionPurity.internalComplex f j B b) U hcover haffine n
  intro a
  obtain ⟨i, hi⟩ := hcoordinate a
  rcases hlocal a with hunit | ⟨rs, hrs, hreg, hlength⟩
  · exact exactAt_of_unit f j B b (U a) (haffine a) i hi hunit n
  · exact ClosedImmersionPurity.exactAt f j B b (U a) (haffine a) i hi
      rs hreg hrs n (by omega)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PurityConcentration
