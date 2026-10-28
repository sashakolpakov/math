import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackRefinement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.UnitCompositionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

/-! # Tensor Refinement Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorRefinementValues

noncomputable section

/-! Refining the target of a section tensor comparison agrees with the tensor comparison for the composite pullback and pulled-back coefficient functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem moduleSectionTensorComparisonApp_refine
    {X Y Z : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (a : X ⟶ Y) (g : Y ⟶ Z) (f : R →+* Γ(Z, ⊤)) (M : Z.Modules) (q : B →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R B) = g.appTop.hom.comp f)
    (U : Z.Opens) (b : B) (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    (Coefficient.PullbackRefinement.coefficientPullbackRefinementMap a g f M).app (.op U)
      (SectionTensorComparison.moduleSectionTensorComparisonApp g f M q hq U (b ⊗ₜ[R] x)) =
        SectionTensorComparison.moduleSectionTensorComparisonApp (a ≫ g) f M (a.appTop.hom.comp q)
          (Coefficient.PullbackRefinement.pullbackCoefficient_compatible_comp a g f q hq) U (b ⊗ₜ[R] x) := by
  let V := g ⁻¹ᵁ U
  let W := (a ≫ g) ⁻¹ᵁ U
  let m : Γ((Scheme.Modules.pullback g).obj M, V) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U x
  let n : Γ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g).obj M), W) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app ((Scheme.Modules.pullback g).obj M)).app V m
  let c : Γ(Y, V) := Y.presheaf.map V.leTop.op (q b)
  let d : Γ(X, W) := X.presheaf.map W.leTop.op (a.appTop (q b))
  have hc : a.app V c = d := (Global.ScalarBaseChange.globalFunction_pullback_restrict a (q b) V).symm
  have hl : ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app ((Scheme.Modules.pullback g).obj M)).app
      V (c • m) = (show Γ(X, W) from a.app V c) • n :=
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app ((Scheme.Modules.pullback g).obj M)).app_smul c m
  have hu : ((Scheme.Modules.pullbackComp a g).hom.app M).app W n =
      ((Scheme.Modules.pullbackPushforwardAdjunction (a ≫ g)).unit.app M).app U x :=
    Pullback.UnitCompositionValues.pullbackUnit_comp_value a g M U x
  change ((Scheme.Modules.pullbackComp a g).hom.app M).app W
    (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app ((Scheme.Modules.pullback g).obj M)).app V (c • m)) =
      d • (show Γ((Scheme.Modules.pullback (a ≫ g)).obj M, W) from
        ((Scheme.Modules.pullbackPushforwardAdjunction (a ≫ g)).unit.app M).app U x)
  exact (congrArg (((Scheme.Modules.pullbackComp a g).hom.app M).app W) hl).trans
    ((congrArg (fun r : Γ(X, W) => ((Scheme.Modules.pullbackComp a g).hom.app M).app W (r • n)) hc).trans
      ((((Scheme.Modules.pullbackComp a g).hom.app M).app_smul d n).trans
        (congrArg (fun z : Γ((Scheme.Modules.pullback (a ≫ g)).obj M, W) => d • z) hu)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorRefinementValues
