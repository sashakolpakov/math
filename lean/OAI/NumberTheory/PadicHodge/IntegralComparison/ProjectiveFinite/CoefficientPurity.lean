import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientLocalPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedCodimension
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ComplementNeighborhood

/-! # Coefficient Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientPurity

noncomputable section

/-! The actual dual negative resolution of finite flat coefficients on a
smooth projective closed subscheme is concentrated in its codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientLocalPurity

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Flat f]
  (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
  (j : σ) (B b : ℕ) (hb : b ≤ B) (g : ℕ)
  [SmoothOfRelativeDimension g (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

include hb in
omit [LinearOrder σ] in
theorem exactAt (q : ℕ) (hq : q ≠ Fintype.card σ - 1 - g) :
    (CoefficientLocalPurity.internalComplex f i j B b).ExactAt q := by
  classical
  let : LocallyOfFiniteType (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) :=
    AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
  let : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian i
  let (m : ℕ) : ((CoefficientLocalPurity.internalComplex f i j B b).X m).IsQuasicoherent :=
    Projective.InternalHomCoherence.term (CoefficientLocalPurity.coefficients f i) j B b hb m
  have hlocal (z : Proj (homogeneousSubmodule σ R)) :
      ∃ (V : (Proj (homogeneousSubmodule σ R)).Opens) (_ : IsAffineOpen V), z ∈ V ∧
        ∃ k : σ, V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k ∧
          (RingHom.ker (i.app V).hom = ⊤ ∨
            ∃ rs : List Γ(Proj (homogeneousSubmodule σ R), V),
              RingHom.ker (i.app V).hom = Ideal.ofList rs ∧
                RingTheory.Sequence.IsWeaklyRegular Γ(Proj (homogeneousSubmodule σ R), V) rs ∧
                  rs.length = Fintype.card σ - 1 - g) := by
    by_cases hz : z ∈ Set.range i
    · obtain ⟨x, rfl⟩ := hz
      obtain ⟨k, V, hV, hVk, hxV, rs, hrs, hreg, hlen⟩ :=
        Smooth.ClosedCodimension.projective_neighborhood i g x
      exact ⟨V, hV, hxV, k, hVk, Or.inr ⟨rs, hrs, hreg.toIsWeaklyRegular, hlen⟩⟩
    · have hz' : z ∈ ⨆ k : σ, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k := by
        rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
        trivial
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hz'
      obtain ⟨V, hV, hVk, hzV, hunit⟩ :=
        Closed.ComplementNeighborhood.exists_affine i (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k) z hk hz
      exact ⟨V, hV, hzV, k, hVk, Or.inl hunit⟩
  choose U hAffine hmem k hk heq using hlocal
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hmem z⟩
  apply Affine.LocalExactness.exactAt_of_cover (CoefficientLocalPurity.internalComplex f i j B b) U hcover hAffine q
  intro z
  rcases heq z with hunit | ⟨rs, hrs, hreg, hlength⟩
  · exact CoefficientLocalPurity.exactAt_of_unit f i j B b (U z) (hAffine z) (k z) (hk z) hunit q
  · exact CoefficientLocalPurity.exactAt f i j B b
      (U z) (hAffine z) (k z) (hk z) rs hreg hrs q (by omega)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientPurity
