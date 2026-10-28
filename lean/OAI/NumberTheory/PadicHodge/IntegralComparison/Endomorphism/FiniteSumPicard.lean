import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.PullbackPowers

/-! # Finite Sum Picard -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumPicard

noncomputable section

/-! Actual Picard-valued quadratic factorization for finite linear
combinations of algebraic endomorphisms. Doubling the endomorphism
allows all tensor exponents to be nonnegative quadratic monomials. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

def crossBundle (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (f g : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left :=
  ((L.pullback (f + g).toMul.hom.hom.left).tensor
    (AlgebraicGeometry.Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual (L.pullback f.toMul.hom.hom.left))).tensor
      (AlgebraicGeometry.Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual (L.pullback g.toMul.hom.hom.left))

theorem crossBundle_class (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (f g : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    Additive.ofMul (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (crossBundle A L f g)) =
      AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing A L f g := by
  change AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L (f + g) -
    AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L f - AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L g = _
  exact (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing_apply A L f g).symm

theorem double_class (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L (2 • f) =
      2 • AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing A L f f := by
  rw [AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass_nsmul A L hsym,
    AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing_self A L hsym, smul_smul]

theorem double_sum_class (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    {ι : Type v} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (a : ι → ℕ) :
    AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L (2 • ∑ i, a i • f i) =
      ∑ i, ∑ j, (2 * (a i * a j)) • AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing A L (f i) (f j) := by
  rw [double_class A L hsym]
  simp only [map_sum, LinearMap.sum_apply, map_nsmul, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing_symmetric A L (f j) (f i)]

theorem double_sum_pullback_class (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    {ι : Type v} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (a : ι → ℕ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (2 • ∑ i, a i • f i).toMul.hom.hom.left) =
      ∏ i, ∏ j, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (crossBundle A L (f i) (f j)) ^ (2 * (a i * a j)) := by
  have h := double_sum_class A L hsym f a
  simp only [← crossBundle_class A L] at h
  exact congrArg Additive.toMul h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumPicard
