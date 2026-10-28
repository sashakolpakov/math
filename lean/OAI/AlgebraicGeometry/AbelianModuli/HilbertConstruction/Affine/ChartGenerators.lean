import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectivePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Chart Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartGenerators

noncomputable section

/-!
Finite generating families in the affine chart rings of finite-type schemes.
This establishes the finite list of local functions that the section
extension argument must realize as ratios.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S X : Scheme.{u}}

/-- The actual map of affine global-function rings is of finite type. -/
theorem affine_globalSections_finiteType (f : X ⟶ S)
    [IsAffine X] [IsAffine S] [LocallyOfFiniteType f] : f.appTop.hom.FiniteType :=
  HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance

/-- An affine chart in a finite-type scheme over an affine base has a finite
ordered family of generators over the base ring. -/
theorem affine_chart_generators (f : X ⟶ S) [IsAffine S] [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := (U.ι ≫ f).appTop.hom.toAlgebra
    ∃ (k : ℕ) (v : Fin k → Γ(U.toScheme, ⊤)),
      Algebra.adjoin Γ(S, ⊤) (Set.range v) = ⊤ := by
  let := (U.ι ≫ f).appTop.hom.toAlgebra
  have : IsAffine U.toScheme := hU
  have : Algebra.FiniteType Γ(S, ⊤) Γ(U.toScheme, ⊤) :=
    affine_globalSections_finiteType (U.ι ≫ f)
  obtain ⟨k, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  refine ⟨k, fun i => φ (MvPolynomial.X i), ?_⟩
  rw [Algebra.adjoin_range_eq_range_aeval]
  have he : MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) = φ :=
    (MvPolynomial.aeval_unique φ).symm
  apply (congrArg AlgHom.range he).trans
  apply top_unique
  intro b _
  exact hφ b

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartGenerators
