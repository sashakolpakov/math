import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleEvaluation

/-! # Tensor Sheafification Charts -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSheafificationCharts.Construction

noncomputable section

/-! Sheafification of tensor products on line-bundle charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

universe u

local instance tensorSheafificationChartsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

theorem isIso_moduleSheafificationUnit_of_iso {X : Scheme.{u}} {P : X.PresheafOfModules}
    {N : X.Modules} (e : P ≅ N.val) : IsIso (SheafRestriction.Construction.moduleSheafificationUnit P) := by
  let l := SheafRestriction.Construction.sheafificationIsoOfLocallyBijective e.hom
  have hi : IsIso l.hom.val := inferInstanceAs
    (IsIso ((Scheme.Modules.toPresheafOfModules X).map l.hom))
  have : IsIso (SheafRestriction.Construction.moduleSheafificationUnit P ≫ l.hom.val) := by
    rw [TensorOpenComparison.Construction.moduleSheafificationUnit_isoOfLocallyBijective]
    infer_instance
  exact IsIso.of_isIso_comp_right _ l.hom.val

theorem isIso_restrictModuleSheafificationUnit {X : Scheme.{u}} (P : X.PresheafOfModules)
    (U : X.Opens) {N : U.toScheme.Modules}
    (e : (SheafRestriction.Construction.restrictModulePresheaf U.ι).obj P ≅ N.val) :
    IsIso ((SheafRestriction.Construction.restrictModulePresheaf U.ι).map (SheafRestriction.Construction.moduleSheafificationUnit P)) := by
  have hu := isIso_moduleSheafificationUnit_of_iso e
  have hi : IsIso (SheafRestriction.Construction.restrictSheafificationIso U.ι P).hom.val := inferInstanceAs
    (IsIso ((Scheme.Modules.toPresheafOfModules U.toScheme).map (SheafRestriction.Construction.restrictSheafificationIso U.ι P).hom))
  have h := TensorOpenComparison.Construction.moduleSheafificationUnit_restrictIso U.ι P
  rw [← h]
  exact IsIso.comp_isIso' hu hi

theorem isIso_moduleSheafificationUnit_app_of_restrictIso {X : Scheme.{u}}
    (P : X.PresheafOfModules) (U : X.Opens) {N : U.toScheme.Modules}
    (e : (SheafRestriction.Construction.restrictModulePresheaf U.ι).obj P ≅ N.val) (V : X.Opens) (hVU : V ≤ U) :
    IsIso ((SheafRestriction.Construction.moduleSheafificationUnit P).app (.op V)) := by
  have hR := isIso_restrictModuleSheafificationUnit P U e
  let W := U.ι ⁻¹ᵁ V
  let q := (SheafRestriction.Construction.restrictModulePresheaf U.ι).map (SheafRestriction.Construction.moduleSheafificationUnit P)
  have hq : IsIso (q.app (.op W)) := inferInstanceAs
    (IsIso ((PresheafOfModules.evaluation _ (.op W)).map q))
  have hp : IsIso ((SheafRestriction.Construction.moduleSheafificationUnit P).app (.op (U.ι ''ᵁ W))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (ConcreteCategory.isIso_iff_bijective (q.app (.op W))).mp hq
  have heq : U.ι ''ᵁ W = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  exact heq ▸ hp

def restrictTensorPresheafTrivialization {X : Scheme.{u}} {M N : X.Modules} (U : X.Opens)
    (eM : M.restrict U.ι ≅ LineBundle.Construction.structureSheafModule U.toScheme)
    (eN : N.restrict U.ι ≅ LineBundle.Construction.structureSheafModule U.toScheme) :
    (SheafRestriction.Construction.restrictModulePresheaf U.ι).obj (M.val ⊗ N.val) ≅
      (LineBundle.Construction.structureSheafModule U.toScheme).val :=
  (TensorRestriction.Construction.restrictPresheafTensorIso U.ι M.val N.val).symm ≪≫
    (((Scheme.Modules.toPresheafOfModules U.toScheme).mapIso eM) ⊗ᵢ
      ((Scheme.Modules.toPresheafOfModules U.toScheme).mapIso eN)) ≪≫
        (λ_ (LineBundle.Construction.structureSheafModule U.toScheme).val)

theorem tensorSheafificationUnit_locally_isIso_app {X : Scheme.{u}} {M N : X.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      IsIso ((SheafRestriction.Construction.moduleSheafificationUnit (M.val ⊗ N.val)).app (.op V)) := by
  intro x
  obtain ⟨U, hxU, ⟨eM⟩⟩ := hM x
  obtain ⟨V, hxV, ⟨eN⟩⟩ := hN x
  let W := U ⊓ V
  let a : M.restrict W.ι ≅ LineBundle.Construction.structureSheafModule W.toScheme :=
    (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M ≪≫
      TensorRestriction.Construction.restrictLineBundleTrivialization inf_le_left eM
  let b : N.restrict W.ι ≅ LineBundle.Construction.structureSheafModule W.toScheme :=
    (Scheme.Modules.restrictFunctorIsoPullback W.ι).app N ≪≫
      TensorRestriction.Construction.restrictLineBundleTrivialization inf_le_right eN
  exact ⟨W, ⟨hxU, hxV⟩, fun V hV ↦ isIso_moduleSheafificationUnit_app_of_restrictIso
    (M.val ⊗ N.val) W (restrictTensorPresheafTrivialization W a b) V hV⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSheafificationCharts.Construction
