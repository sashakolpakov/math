import OAI.AlgebraicGeometry.Picard.PoincareBundle.TripleTensorPowerIso
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PositiveFormula

/-! # Positive Formula Powers -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaPowers

noncomputable section

/-! Positive tensor powers of the original ample inducing-line formula remain actual positive formulas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

/-- Tensoring the original formula gives the exact formula for the powered inducing line. -/
def formula_power
    (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (L.pullback (fst A A).left).sheaf)
      (L.pullback (snd A A).left).sheaf ≅ (L.pullback μ[A].left).sheaf) (n : ℕ) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Q.tensorPower n).sheaf ((L.tensorPower n).pullback (fst A A).left).sheaf)
      ((L.tensorPower n).pullback (snd A A).left).sheaf ≅ ((L.tensorPower n).pullback μ[A].left).sheaf :=
  AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) (Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso (fst A A).left L n)) (Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso (snd A A).left L n) ≪≫
    TripleTensorPowerIso.iso Q (L.pullback (fst A A).left) (L.pullback (snd A A).left) n ≪≫
    (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor (A ⊗ A).left n).mapIso e ≪≫ (Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso μ[A].left L n).symm

/-- The original zero rigidification gives a zero rigidification of every tensor power. -/
def zero_power (e : (L.pullback η[A].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k))) (n : ℕ) :
    ((L.tensorPower n).pullback η[A].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k)) :=
  Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso η[A].left L n ≪≫ (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor (Spec (.of k)) n).mapIso e ≪≫ AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso _ n

omit L in
/-- This constructs the ample line and both normalized formula isomorphisms for each positive power. -/
theorem positive_power (h : AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A Q) (n : ℕ) (hn : 0 < n) :
    AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A (Q.tensorPower n) := by
  obtain ⟨L, hL, ⟨e0⟩, ⟨e⟩⟩ := h
  exact ⟨L.tensorPower n, hL.tensorPower n hn, ⟨zero_power A L e0 n⟩, ⟨formula_power A Q L e n⟩⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaPowers
