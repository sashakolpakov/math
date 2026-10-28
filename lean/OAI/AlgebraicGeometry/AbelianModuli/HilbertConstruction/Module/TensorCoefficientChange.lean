import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorRefinementValues

/-! # Tensor Coefficient Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorCoefficientChange

noncomputable section

/-! Section tensor comparisons commute with algebra maps on the scalar factor and with actual refinement of the pullback scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u

variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C]

theorem moduleSectionTensorComparisonApp_coefficient_change
    {X Y : Scheme.{u}} (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : X.Modules)
    (q : B →+* Γ(Y, ⊤)) (r : C →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f)
    (hr : r.comp (algebraMap R C) = a.appTop.hom.comp f)
    (α : B →ₐ[R] C) (hα : r.comp α.toRingHom = q)
    (U : X.Opens) (b : B) (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    SectionTensorComparison.moduleSectionTensorComparisonApp a f M r hr U (α b ⊗ₜ[R] x) =
      SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq U (b ⊗ₜ[R] x) := by
  let y : Γ((Scheme.Modules.pullback a).obj M, a ⁻¹ᵁ U) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app U x
  change Y.presheaf.map (a ⁻¹ᵁ U).leTop.op (r (α b)) •
      y =
    Y.presheaf.map (a ⁻¹ᵁ U).leTop.op (q b) •
      y
  rw [show r (α b) = q b from DFunLike.congr_fun hα b]

theorem moduleSectionTensorComparisonApp_refine_coefficient_change
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (g : Y ⟶ Z)
    (f : R →+* Γ(Z, ⊤)) (M : Z.Modules)
    (q : B →+* Γ(Y, ⊤)) (r : C →+* Γ(X, ⊤))
    (hq : q.comp (algebraMap R B) = g.appTop.hom.comp f)
    (hr : r.comp (algebraMap R C) = (a ≫ g).appTop.hom.comp f)
    (α : B →ₐ[R] C) (hα : r.comp α.toRingHom = a.appTop.hom.comp q)
    (U : Z.Opens) (b : B) (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    (Coefficient.PullbackRefinement.coefficientPullbackRefinementMap a g f M).app (.op U)
      (SectionTensorComparison.moduleSectionTensorComparisonApp g f M q hq U (b ⊗ₜ[R] x)) =
        SectionTensorComparison.moduleSectionTensorComparisonApp (a ≫ g) f M r hr U (α b ⊗ₜ[R] x) :=
  (TensorRefinementValues.moduleSectionTensorComparisonApp_refine a g f M q hq U b x).trans
    (moduleSectionTensorComparisonApp_coefficient_change (a ≫ g) f M
      (a.appTop.hom.comp q) r (Coefficient.PullbackRefinement.pullbackCoefficient_compatible_comp a g f q hq) hr α hα U b x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorCoefficientChange
