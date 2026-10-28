import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleScalarTensorMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorComparison

/-! # Tensor Linearity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.TensorLinearity

noncomputable section

/-! The canonical tensor extension intertwines multiplication on the new
coefficient ring with its specified action on the target. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u

theorem compatibleScalarTensorMap_smul
    {R B V G : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup V] [Module R V] [AddCommGroup G] [Module R G]
    (ρ : B →+* Module.End R G) (hρ : ∀ (r : R) (x : G), ρ (algebraMap R B r) x = r • x)
    (a : V →ₗ[R] G) (b : B) (z : B ⊗[R] V) :
    CompatibleScalarTensorMap.compatibleScalarTensorMap ρ hρ a (b • z) = ρ b (CompatibleScalarTensorMap.compatibleScalarTensorMap ρ hρ a z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c v =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, CompatibleScalarTensorMap.compatibleScalarTensorMap_tmul,
        CompatibleScalarTensorMap.compatibleScalarTensorMap_tmul, map_mul]
      rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem moduleSectionTensorComparisonApp_smul
    {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f)
    (U : X.Opens) (b : B) (z : B ⊗[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    HilbertConstruction.Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq U (b • z) =
      Section.PresheafExtendedScalars.pushedCoefficientScalarComponent a f ((Scheme.Modules.pullback a).obj M) q U b
        (HilbertConstruction.Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq U z) :=
  compatibleScalarTensorMap_smul _ _ _ b z

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.TensorLinearity
