import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.PositiveFormula

/-! # Fiber Formula Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberFormulaRecovery

noncomputable section

/-! The positive formula for the base-changed dual is exactly positivity on the original geometric fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {a : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)
  (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S)

/-- The actual pulled Poincare bundle agrees with the bundle defining geometric positivity. -/
def familyIso :
    ((D.pullback s).poincare.pullback (((Over.pullback s).map p) ⊗ₘ 𝟙 (A.pullback s).scheme).left).sheaf ≅
      (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s).sheaf :=
  (Scheme.Modules.pullbackComp (((Over.pullback s).map p) ⊗ₘ 𝟙 (A.pullback s).scheme).left
    (D.poincarePullbackOverMap s).left).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (congrArg
        (fun t => (((Over.pullback s).map p) ⊗ₘ 𝟙 (A.pullback s).scheme).left ≫ t)
        (AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap D s).symm)).app D.poincare.sheaf

/-- Ground positivity for the pulled-back map yields the original geometric-fiber clause. -/
theorem positive (hp : AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula (A.pullback s).scheme
    ((D.pullback s).poincare.pullback (((Over.pullback s).map p) ⊗ₘ 𝟙 (A.pullback s).scheme).left)) :
    AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p K s := by
  obtain ⟨L, hL, ho, ⟨he⟩⟩ := hp
  exact ⟨L, hL, ho, ⟨AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (familyIso D p K s).symm (Iso.refl _))
    (Iso.refl _) ≪≫ he⟩⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberFormulaRecovery
