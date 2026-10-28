import OAI.RepresentationTheory.Theta.Geometric.SquareZero.SchemeFactorization
import OAI.RepresentationTheory.Theta.Geometric.SquareZero.ParameterSeparation

/-! # Relative Kernel -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.RelativeKernel

noncomputable section

/-! A normalized Picard family with injective dual-number parameters
has no relative kernel over any square-zero ideal of any complex algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] SquareZero.Ideal.idealCoefficientOppositeModule SquareZero.Ideal.idealCoefficientCentralScalar

theorem squareZeroIdeal_quotient_nontrivial {R : Type} [CommRing R] [Nontrivial R]
    (I : Ideal R) (hI : I * I = ⊥) : Nontrivial (R ⧸ I) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  have h1 : (1 : R) ∈ I := by rw [h]; trivial
  have h2 : (1 : R) * 1 = 0 := (Submodule.mem_bot R).mp (hI ▸ Ideal.mul_mem_mul h1 h1)
  exact one_ne_zero (by simpa only [one_mul] using h2)

set_option backward.isDefEq.respectTransparency false in
theorem parameterPicardClass_squareZero_relative_kernel
    {R : Type} [CommRing R] [Algebra ℂ R] [Nontrivial R]
    (I : Ideal R) (hI : I * I = ⊥)
    {n : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eQ : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    (hinj : Function.Injective (fun t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t))
    (r : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ P)
    (hr : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (R ⧸ I) (Ideal.Quotient.mkₐ ℂ I) ≫ r = 1)
    (hQ : ParameterizedPicardClass.parameterPicardClass Q r = ParameterizedPicardClass.parameterPicardClass Q (1 : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ P)) : r = 1 := by
  have : Nontrivial (R ⧸ I) := squareZeroIdeal_quotient_nontrivial I hI
  have hr' : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (R ⧸ I) (Ideal.Quotient.mkₐ ℂ I) ≫ r =
      toUnit (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⧸ I)) ≫ (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) := by
    rw [hr]
    simp
  obtain ⟨a, ha⟩ := SchemeFactorization.squareZero_schemeTest_factorization I hI P r 1 hr'
  let i : I →ₗ[ℂ] R := (I.restrictScalars ℂ).subtype
  have hs : ∀ x y : I, i x * i y = 0 := by
    intro x y
    exact (Submodule.mem_bot R).mp (hI ▸ Ideal.mul_mem_mul x.property y.property)
  have ha' : Normalized.SquareZeroDescent.complexSquareZeroParameterMap i hs ≫ a = r := ha
  have ha1 : a = 1 := by
    apply ParameterSeparation.parameterPicardClass_squareZero_composite_injective i Subtype.val_injective hs
      (Ideal.Quotient.mkₐ ℂ I) (SquareZero.Ideal.squareZeroIdeal_exact I) A Q eQ hinj
    dsimp only
    rw [ha']
    simpa using hQ
  simpa [ha1] using ha'.symm

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.RelativeKernel
