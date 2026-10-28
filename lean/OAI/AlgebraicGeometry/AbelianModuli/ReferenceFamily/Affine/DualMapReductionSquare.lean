import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftReduction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.SelfLiftDerivations
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ChartCoefficientConormal

/-! # Dual Map Reduction Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualMapReductionSquare

noncomputable section

/-! The first-coefficient equation for a map of dual tests is the
literal square of their original affine-scheme reduction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

section
variable (k B C : Type) [CommRing k] [CommRing B] [CommRing C] [Algebra k B] [Algebra k C]

theorem affineDualMap_reduction_square (q : B →ₐ[k] C) (f : DualNumber B →ₐ[k] DualNumber C)
    (h : ∀ u, (f u).fst = q u.fst) :
    Dual.CoefficientSchemeTests.dualCoefficientOrigin k C ≫ AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber B) (DualNumber C) f =
      AlgebraAutomorphismNaturality.affineOverAlgHom k B C q ≫ Dual.CoefficientSchemeTests.dualCoefficientOrigin k B := by
  change AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) C (TrivSqZeroExt.fstHom k C C) ≫
      AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber B) (DualNumber C) f =
    AlgebraAutomorphismNaturality.affineOverAlgHom k B C q ≫ AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber B) B (TrivSqZeroExt.fstHom k B B)
  rw [OverMorphismAlgebra.affineOverAlgHom_comp, OverMorphismAlgebra.affineOverAlgHom_comp]
  congr 1
  exact AlgHom.ext h

end

theorem affineChartCoefficientPoint_self (k B : Type) [Field k] [CommRing B] [Algebra k B]
    (A : Over (Spec (.of k))) (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ A) [IsOpenImmersion i.left] :
    ChartCoefficientConormal.affineChartCoefficientPoint k B B A i = i := by
  unfold ChartCoefficientConormal.affineChartCoefficientPoint
  rw [SelfLiftDerivations.affineOverAlgHom_self, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualMapReductionSquare
