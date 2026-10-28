import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalSections

/-! # Coefficient Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoefficientSections

noncomputable section

/-! Over a chosen coefficient ring, actual global frame-sheaf sections inject into chart functions, with image exactly the transition-compatible tuples. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {R : Type u} [CommRing R]
variable (U : ι → X.Opens) (f : R →+* Γ(X, ⊤))

def openFrameCoefficientTupleEquiv :
    (ModuleCat.restrictScalars f).obj (ModuleCat.of Γ(X, ⊤) (GlobalTuples.OpenFrameGlobalTuple U)) ≃ₗ[R]
      ((i : ι) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections f (U i)) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {U} (D : Transitions.OpenFrameTransitions U)

def openFrameGlobalTupleMap :
    (Global.RingModulePresheaf.globalRingModulePresheaf (ModuleSheaf.openFrameModuleSheaf D)).obj (.op ⊤) →ₗ[Γ(X, ⊤)] GlobalTuples.OpenFrameGlobalTuple U :=
  (GlobalCompatibility.openFrameGlobalCompatibleModule D).subtype.comp (GlobalSections.openFrameGlobalSectionsEquiv D).toLinearMap

def openFrameCoefficientGlobalTupleMap :
    (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f).obj (ModuleSheaf.openFrameModuleSheaf D) →ₗ[R]
      ((i : ι) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections f (U i)) :=
  (openFrameCoefficientTupleEquiv U f).toLinearMap.comp
    ((ModuleCat.restrictScalars f).map (ModuleCat.ofHom (openFrameGlobalTupleMap D))).hom

theorem openFrameCoefficientGlobalTupleMap_injective :
    Function.Injective (openFrameCoefficientGlobalTupleMap f D) :=
  Subtype.val_injective.comp (GlobalSections.openFrameGlobalSectionsEquiv D).injective

theorem openFrameCoefficientGlobalTupleMap_range
    (x : (i : ι) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections f (U i)) :
    (∃ s, openFrameCoefficientGlobalTupleMap f D s = x) ↔ Frame.TransitionEquations.FrameCompatible D x := by
  constructor
  · rintro ⟨s, rfl⟩
    exact (GlobalCompatibility.openFrameGlobalCompatibleModule_mem D _).mp (GlobalSections.openFrameGlobalSectionsEquiv D s).property
  · intro hx
    let y : GlobalCompatibility.openFrameGlobalCompatibleModule D := ⟨x, (GlobalCompatibility.openFrameGlobalCompatibleModule_mem D x).mpr hx⟩
    refine ⟨(GlobalSections.openFrameGlobalSectionsEquiv D).symm y, ?_⟩
    exact congrArg Subtype.val ((GlobalSections.openFrameGlobalSectionsEquiv D).apply_symm_apply y)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoefficientSections
