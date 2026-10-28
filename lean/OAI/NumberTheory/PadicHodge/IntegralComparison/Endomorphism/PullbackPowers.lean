import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd

/-! # Pullback Powers -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.PullbackPowers

noncomputable section

/-! Pullback along `[n] - f` is an actual quadratic tensor orbit. The
three fixed line bundles are constructed from `L`, `f`, and `1 - f`.
This identity holds in arbitrary characteristic over an algebraically
closed field and does not use cohomological comparison or isogeny degrees. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

theorem class_nsmul_sub (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f g : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ) :
    AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L (n • f - g) =
      (n * n) • AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L f -
        n • AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing A L f g + AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L g := by
  have hp : AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing A L (n • f) (-g) =
      -(n • AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing A L f g) := by
    rw [map_nsmul, LinearMap.smul_apply, map_neg, smul_neg]
  calc
    AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L (n • f - g) =
        AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing A L (n • f) (-g) +
          AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L (n • f) + AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L (-g) := by
      rw [AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing_apply, sub_eq_add_neg]
      abel
    _ = _ := by
      rw [hp, AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass_nsmul A L hsym,
        AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass_neg A L hsym]
      abel

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem class_one (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L 1 = Additive.ofMul (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
  change Additive.ofMul (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 A.left) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]

/-- The line bundle giving the linear term in the `[n] - f` tensor orbit. -/
def linearBundle (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left :=
  ((L.pullback (1 - f).toMul.hom.hom.left).tensor (AlgebraicGeometry.Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L)).tensor
    (AlgebraicGeometry.Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual (L.pullback f.toMul.hom.hom.left))

theorem linearBundle_class (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    Additive.ofMul (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (linearBundle A L f)) =
      -AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardBilinear.Construction.algebraicEndPicardPairing A L 1 f := by
  have hc := class_nsmul_sub A L hsym 1 f 1
  simp only [one_nsmul, one_mul, class_one] at hc
  change AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L (1 - f) -
    Additive.ofMul (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) - AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L f = _
  rw [hc]
  abel

/-- The fixed tensor factors of the actual pullback along `[n] - f`. -/
def tensorOrbit (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left :=
  ((L.tensorPower (n * n)).tensor ((linearBundle A L f).tensorPower n)).tensor
    (L.pullback f.toMul.hom.hom.left)

theorem pullback_class (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (tensorOrbit A L f n) := by
  apply Additive.ofMul.injective
  change AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f) =
    Additive.ofMul (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower (n * n))) +
      Additive.ofMul (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((linearBundle A L f).tensorPower n)) +
      AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L f
  rw [AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_pow, AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd.Construction.PicardPowers.class_pow]
  change AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f) =
    (n * n) • Additive.ofMul (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) +
      n • Additive.ofMul (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (linearBundle A L f)) +
      AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction.algebraicEndLineBundleClass A L f
  rw [linearBundle_class A L hsym, smul_neg]
  simpa only [nsmul_one, class_one, sub_eq_add_neg] using class_nsmul_sub A L hsym 1 f n

/-- An isomorphism of the genuine sheaves, rather than only their numerical classes. -/
theorem pullback_iso (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ) :
    Nonempty ((L.pullback ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - f).toMul.hom.hom.left).sheaf ≅
      (tensorOrbit A L f n).sheaf) :=
  Quotient.exact (pullback_class A L hsym f n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.PullbackPowers
