import OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ComplementaryIsogeny
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EffectiveOverQuotient
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarClasses
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMapCongruence

/-! # Shared Dual Complement -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedDualComplement

noncomputable section

/-! The complementary dual map is constructed from the actual quotient's torsion kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMaps

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  (DA : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (DB : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B)
  (Qh : FiberwiseMultiplication.Multiplication (fst DB.abelian B) (snd DB.abelian B) (Line.Comparison.Bundle.fromShared DB.poincare))
  (Qv : FiberwiseMultiplication.Multiplication (snd DB.abelian B) (fst DB.abelian B) (Line.Comparison.Bundle.fromShared DB.poincare))
  (f : A ⟶ B) [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  (n : ℕ) (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)

include Qh Qv hker

/-- The actual represented dual quotient has a constructed scalar complement. -/
theorem exists_dual_complement : ∃ v : DA.abelian ⟶ DB.abelian,
    DualMaps.representedDualMap (SharedRepresentation.representation DA) (SharedRepresentation.representation DB) f ≫ v = (𝟙 DB.abelian) ^ n := by
  have : EffectiveEpi f := EffectiveOverQuotient.affine_effective f
  have : EffectiveEpi (f ⊗ₘ f) := EffectiveOverQuotient.tensor_effective f
  let t := ComplementaryIsogeny.complement f n hker
  have : IsMonHom t := ComplementaryIsogeny.complement_isMonHom f n hker
  refine ⟨DualMaps.representedDualMap (SharedRepresentation.representation DB) (SharedRepresentation.representation DA) t, ?_⟩
  rw [← DualMaps.representedDualMap_comp]
  exact (DualMapCongruence.representedDualMap_congr (SharedRepresentation.representation DB) (SharedRepresentation.representation DB) _ _
    (ComplementaryIsogeny.right_complement f n hker)).trans
    (Poincare.ScalarClasses.representedDualMap_scalar (Line.Comparison.Bundle.fromShared DB.poincare) Qh Qv (SharedRepresentation.representation DB)
      (SharedRepresentation.universalClass DB (Vertical.ProductParameters.globalProduct DB.abelian B (Line.Comparison.Bundle.fromShared DB.poincare) Qv)
        (Vertical.ProductParameters.globalProduct_isIso DB.abelian B (Line.Comparison.Bundle.fromShared DB.poincare) Qv)) n)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedDualComplement
