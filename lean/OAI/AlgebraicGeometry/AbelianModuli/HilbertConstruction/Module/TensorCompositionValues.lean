import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitCompositionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionValues

/-! # Tensor Composition Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorCompositionValues

noncomputable section

/-! The actual module-section tensor comparison respects successive pullbacks under the canonical composition isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem moduleSectionTensorComparisonApp_comp
    {X Y Z : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (a : Z ⟶ Y) (j : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Z, ⊤))
    (hq : q.comp (algebraMap R B) = (a ≫ j).appTop.hom.comp f)
    (hq' : q.comp (algebraMap R B) = a.appTop.hom.comp (j.appTop.hom.comp f))
    (U : X.Opens) (b : B) (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    ((Scheme.Modules.pullbackComp a j).hom.app M).app ((a ≫ j) ⁻¹ᵁ U)
      (SectionTensorComparison.moduleSectionTensorComparisonApp a (j.appTop.hom.comp f) ((Scheme.Modules.pullback j).obj M) q hq'
        (j ⁻¹ᵁ U) (b ⊗ₜ[R] Coefficient.PullbackSectionValues.coefficientPullbackSectionValueMap j f M U x)) =
      SectionTensorComparison.moduleSectionTensorComparisonApp (a ≫ j) f M q hq U (b ⊗ₜ[R] x) := by
  let W := (a ≫ j) ⁻¹ᵁ U
  let v : Γ((Scheme.Modules.pullback j).obj M, j ⁻¹ᵁ U) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app U x
  let w : Γ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback j).obj M), W) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app ((Scheme.Modules.pullback j).obj M)).app (j ⁻¹ᵁ U) v
  let r : Γ(Z, W) := Z.presheaf.map W.leTop.op (q b)
  have hu : ((Scheme.Modules.pullbackComp a j).hom.app M).app W w =
      ((Scheme.Modules.pullbackPushforwardAdjunction (a ≫ j)).unit.app M).app U x :=
    Pullback.UnitCompositionValues.pullbackUnit_comp_value a j M U x
  change ((Scheme.Modules.pullbackComp a j).hom.app M).app W (r • w) =
    r • (show Γ((Scheme.Modules.pullback (a ≫ j)).obj M, W) from
      ((Scheme.Modules.pullbackPushforwardAdjunction (a ≫ j)).unit.app M).app U x)
  exact (((Scheme.Modules.pullbackComp a j).hom.app M).app_smul r w).trans
    (congrArg (fun z : Γ((Scheme.Modules.pullback (a ≫ j)).obj M, W) => r • z) hu)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorCompositionValues
