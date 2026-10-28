import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentBasePoint

/-! # Base Tangent Tests -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.BaseTangentTests

noncomputable section

/-! Actual tangent points as test maps over the coefficient field.
Their zero vector is the constant reduction, and equality of test maps
detects equality of the original derivations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k]

def affineDualConstant : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber k) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber k) :=
  Over.homMk (Smooth.AffineDualProduct.dualBaseProjection k ≫ Smooth.AffineDualProduct.dualBaseReduction k) (by
    change (Smooth.AffineDualProduct.dualBaseProjection k ≫ Smooth.AffineDualProduct.dualBaseReduction k) ≫ Smooth.AffineDualProduct.dualBaseProjection k = Smooth.AffineDualProduct.dualBaseProjection k
    rw [Category.assoc, Normalized.SmoothAffineDualProduct.dualBaseReduction_projection, Category.comp_id])

variable (R : Type) [CommRing R] [Algebra k R] [Algebra R k] [IsScalarTower k R k]

def affineBaseTangentTest (d : Derivation k R k) : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber k) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k R :=
  Over.homMk (TangentBasePoint.tangentBasePoint k R d) (TangentBasePoint.tangentBasePoint_overField k R d)

theorem affineBaseTangentTest_injective : Function.Injective (affineBaseTangentTest k R) := by
  intro d e h
  exact TangentBasePoint.tangentBasePoint_injective k R (congrArg Over.Hom.left h)

theorem affineBaseTangentTest_zero_constant (d : Derivation k R k) :
    affineBaseTangentTest k R 0 = affineDualConstant k ≫ affineBaseTangentTest k R d := by
  apply Over.OverMorphism.ext
  exact (TangentBasePoint.tangentBasePoint_zero_constant k R d).trans (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.BaseTangentTests
