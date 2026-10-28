import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientSchemeTests
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OverMorphismAlgebra
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients

/-! # Coefficient Map Squares -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientMapSquares

noncomputable section

/-! The literal maps between dual-number test schemes commute with
their reductions and projections under coefficient change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k C C' : Type) [CommRing k] [CommRing C] [CommRing C'] [Algebra k C] [Algebra k C']
    (q : C →ₐ[k] C')

theorem dualCoefficientOrigin_natural :
    CoefficientSchemeTests.dualCoefficientOrigin k C' ≫ Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (NumberCoefficients.dualNumberAlgMap q) =
      Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C C' q ≫ CoefficientSchemeTests.dualCoefficientOrigin k C := by
  change Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C') C' (TrivSqZeroExt.fstHom k C' C') ≫
      Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (NumberCoefficients.dualNumberAlgMap q) =
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C C' q ≫ Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) C (TrivSqZeroExt.fstHom k C C)
  rw [Affine.OverMorphismAlgebra.affineOverAlgHom_comp, Affine.OverMorphismAlgebra.affineOverAlgHom_comp]
  exact congrArg (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) C') (AlgHom.ext (fun _ => rfl))

theorem dualCoefficientProjection_natural :
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (NumberCoefficients.dualNumberAlgMap q) ≫ CoefficientSchemeTests.dualCoefficientProjection k C =
      CoefficientSchemeTests.dualCoefficientProjection k C' ≫ Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C C' q := by
  change Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) (DualNumber C') (NumberCoefficients.dualNumberAlgMap q) ≫
      Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C (DualNumber C) (TrivSqZeroExt.inlAlgHom k C C) =
    Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C' (DualNumber C') (TrivSqZeroExt.inlAlgHom k C' C') ≫ Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C C' q
  rw [Affine.OverMorphismAlgebra.affineOverAlgHom_comp, Affine.OverMorphismAlgebra.affineOverAlgHom_comp]
  apply congrArg (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C (DualNumber C'))
  apply AlgHom.ext
  intro c
  apply TrivSqZeroExt.ext
  · rfl
  · exact map_zero q

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientMapSquares
