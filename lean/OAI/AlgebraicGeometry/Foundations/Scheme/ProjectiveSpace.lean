import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Basic.Complex.Basic

/-! # Projective Space -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace

noncomputable section

/-!
# Standard complex projective space

The scheme is literally the projective spectrum of the polynomial ring with
its standard grading. Its structure map uses the proved identification of the
degree-zero ring with the complex numbers.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The base scheme for complex algebraic geometry. -/
abbrev complexBase : Scheme := Spec (.of ℂ)

/-- The standard homogeneous coordinate ring in `n + 1` variables. -/
abbrev homogeneousCoordinateRing (n : ℕ) := MvPolynomial (Fin (n + 1)) ℂ

/-- The usual grading by total degree. -/
abbrev projectiveGrading (n : ℕ) : ℕ → Submodule ℂ (homogeneousCoordinateRing n) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ

instance projectiveGradedAlgebra (n : ℕ) : GradedAlgebra (projectiveGrading n) :=
  MvPolynomial.gradedAlgebra

/-- Complex projective `n`-space as the genuine scheme `Proj ℂ[X₀,...,Xₙ]`. -/
abbrev projectiveSpace (n : ℕ) : Scheme := AlgebraicGeometry.Proj (projectiveGrading n)

/-- The degree-zero ring of the homogeneous coordinate ring consists exactly
of the constant complex polynomials. -/
def degreeZeroConstants (n : ℕ) : ℂ ≃+* projectiveGrading n 0 where
  toFun z := ⟨MvPolynomial.C z, MvPolynomial.isHomogeneous_C (Fin (n + 1)) z⟩
  invFun p := p.val.coeff 0
  left_inv z := MvPolynomial.coeff_zero_C z
  right_inv p := by
    apply Subtype.ext
    have hp : MvPolynomial.IsHomogeneous p.val 0 := p.property
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).mpr hp)).symm
  map_mul' z w := by
    apply Subtype.ext
    exact map_mul MvPolynomial.C z w
  map_add' z w := by
    apply Subtype.ext
    exact map_add MvPolynomial.C z w

@[simp]
theorem degreeZeroConstants_coe (n : ℕ) (z : ℂ) :
    (degreeZeroConstants n z : homogeneousCoordinateRing n) = MvPolynomial.C z := rfl

@[simp]
theorem degreeZeroConstants_symm_apply (n : ℕ) (p : projectiveGrading n 0) :
    (degreeZeroConstants n).symm p = p.val.coeff 0 := rfl

/-- The standard structure morphism `ℙⁿ_ℂ → Spec ℂ`. -/
def projectiveSpaceToBase (n : ℕ) : projectiveSpace n ⟶ complexBase :=
  Proj.toSpecZero (projectiveGrading n) ≫
    Spec.map (CommRingCat.ofHom (degreeZeroConstants n).toRingHom)

/-- On every standard homogeneous chart, the structure morphism is induced
by constants followed by the canonical map to the degree-zero localization. -/
theorem projectiveSpaceToBase_chart (n : ℕ) (m : ℕ)
    (f : homogeneousCoordinateRing n) (hf : f ∈ projectiveGrading n m) (hm : 0 < m) :
    Proj.awayι (projectiveGrading n) f hf hm ≫ projectiveSpaceToBase n =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (projectiveGrading n) (Submonoid.powers f)).comp
          (degreeZeroConstants n).toRingHom)) := by
  rw [projectiveSpaceToBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
