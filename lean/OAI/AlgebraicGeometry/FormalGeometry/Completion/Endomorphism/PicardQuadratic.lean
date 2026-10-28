import OAI.AlgebraicGeometry.FormalGeometry.Completion.CubeIdentity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms
import OAI.AlgebraicGeometry.FormalGeometry.Completion.AmplePullbackDetection

/-! # Picard Quadratic -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction

noncomputable section

/-! Pullback of a symmetric line bundle is a quadratic function on the
actual endomorphism group, with values in the actual Picard group. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

def algebraicEndLineBundleClass (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (f : Endomorphisms.Construction.AlgebraicEnd A) :
    Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.left) :=
  Additive.ofMul (Quotients.FiniteDescent.CubicalMultiplicationIs.Construction.CubicalMultiplication.pullbackClass A L f.toMul.hom.hom)

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem algebraicEndLineBundleClass_zero (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    algebraicEndLineBundleClass A L 0 = 0 :=
  Quotients.FiniteDescent.CubicalMultiplicationIs.Construction.CubicalMultiplication.class_one A L

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem algebraicEndLineBundleClass_neg (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : Endomorphisms.Construction.AlgebraicEnd A) :
    algebraicEndLineBundleClass A L (-f) = algebraicEndLineBundleClass A L f :=
  Quotients.FiniteDescent.CubicalMultiplicationIs.Construction.CubicalMultiplication.class_inv A L hsym f.toMul.hom.hom

theorem algebraicEndLineBundleClass_cube (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (f g h : Endomorphisms.Construction.AlgebraicEnd A) :
    algebraicEndLineBundleClass A L (f + g + h) + algebraicEndLineBundleClass A L f +
      algebraicEndLineBundleClass A L g + algebraicEndLineBundleClass A L h =
      algebraicEndLineBundleClass A L (f + g) + algebraicEndLineBundleClass A L (f + h) +
        algebraicEndLineBundleClass A L (g + h) :=
  CubeIdentity.Construction.lineBundle_isCubical A L f.toMul.hom.hom g.toMul.hom.hom h.toMul.hom.hom

theorem algebraicEndLineBundleClass_parallelogram (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f g : Endomorphisms.Construction.AlgebraicEnd A) :
    algebraicEndLineBundleClass A L (f + g) + algebraicEndLineBundleClass A L (f - g) =
      2 • algebraicEndLineBundleClass A L f + 2 • algebraicEndLineBundleClass A L g :=
  Quotients.FiniteDescent.CubicalAlgebraPow.Construction.CubicalAlgebra.parallelogram (algebraicEndLineBundleClass A L)
    (algebraicEndLineBundleClass_zero A L) (algebraicEndLineBundleClass_neg A L hsym)
    (algebraicEndLineBundleClass_cube A L) f g

theorem algebraicEndLineBundleClass_nsmul (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (f : Endomorphisms.Construction.AlgebraicEnd A) (n : ℕ) :
    algebraicEndLineBundleClass A L (n • f) = (n * n) • algebraicEndLineBundleClass A L f :=
  Quotients.FiniteDescent.CubicalAlgebraPow.Construction.CubicalAlgebra.nsmul (algebraicEndLineBundleClass A L)
    (algebraicEndLineBundleClass_zero A L) (algebraicEndLineBundleClass_neg A L hsym)
    (algebraicEndLineBundleClass_cube A L) f n

omit [Smooth A.hom] in
/-- An ample line bundle detects the zero actual endomorphism by its pullback class. -/
theorem algebraicEndLineBundleClass_eq_zero_iff (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (hL : L.IsAmple)
    (f : Endomorphisms.Construction.AlgebraicEnd A) : algebraicEndLineBundleClass A L f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback f.toMul.hom.hom.left) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.left) := congrArg Additive.toMul h
    obtain ⟨e⟩ := Quotient.exact hc
    have hf := AmplePullbackDetection.Construction.groupHom_eq_one_of_trivial_ample_pullback f.toMul.hom.hom L hL e
    apply Additive.toMul.injective
    apply Grp.hom_ext
    exact hf
  · rintro rfl
    exact algebraicEndLineBundleClass_zero A L

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.PicardQuadratic.Construction
