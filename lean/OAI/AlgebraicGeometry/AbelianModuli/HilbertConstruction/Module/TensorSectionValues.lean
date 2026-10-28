import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorComparison

/-! # Tensor Section Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorSectionValues

noncomputable section

/-! Pure tensors in the module-section comparison have their explicit sheaf-section value: the changed-base scalar times the adjunction-unit pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem moduleSectionTensorComparisonApp_value
    {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f) (U : X.Opens) (b : B)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    (show Γ((Scheme.Modules.pullback a).obj M, a ⁻¹ᵁ U) from
      SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq U (b ⊗ₜ[R] x)) =
        Y.presheaf.map (a ⁻¹ᵁ U).leTop.op (q b) •
          (show Γ((Scheme.Modules.pullback a).obj M, a ⁻¹ᵁ U) from
            ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app U x) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorSectionValues
