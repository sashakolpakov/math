import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CechSectionBaseChange
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CochainBaseChangeCycles

/-! # Cech Model Section Compatibility -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CechModelSectionCompatibility.Construction

noncomputable section

/-! The sections computed by a universal Cech model have the canonical base-change map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

universe u

private theorem surjective_iff_of_equiv_square {A B C D : Type*}
    (e : A ≃ B) (e' : C ≃ D) (a : A → C) (b : B → D)
    (h : ∀ x, e' (a x) = b (e x)) : Function.Surjective a ↔ Function.Surjective b := by
  constructor
  · intro ha y
    obtain ⟨x, hx⟩ := ha (e'.symm y)
    exact ⟨e x, (h x).symm.trans ((congrArg e' hx).trans (e'.apply_symm_apply y))⟩
  · intro hb y
    obtain ⟨x, hx⟩ := hb (e' y)
    exact ⟨e.symm x, e'.injective ((h (e.symm x)).trans
      ((congrArg b (e.apply_symm_apply x)).trans hx))⟩

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U) [QuasiIsoAt φ 0]
variable [QuasiIsoAt (AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ) 0]

theorem cechModel_sections_baseChange (x : (D.d 0 1).hom.ker) :
    AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g h M U hU φ
        (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle g.appTop.hom D x) =
      OpenPullbackSections.Construction.modulePullbackSection f M ⊤ (AlgebraicGeometry.Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv π M U hU φ x) := by
  let V := fun i ↦ f ⁻¹ᵁ U i
  have hV : iSup V = ⊤ := by
    rw [← f.preimage_iSup, hU]
    rfl
  let e := AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechZeroGluing.Construction.OrderedCechZeroCoordinates.sectionsEquiv ρ
    ((Scheme.Modules.pullback f).obj M) V hV
  apply e.injective
  apply Subtype.ext
  have hc := AlgebraicGeometry.Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.coordinate ρ ((Scheme.Modules.pullback f).obj M)
    V hV (AlgebraicGeometry.Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap f π ρ g h M U φ)
    (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle g.appTop.hom D x)
  change AlgebraicGeometry.Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map ρ ((Scheme.Modules.pullback f).obj M) V
    (AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g h M U hU φ
      (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle g.appTop.hom D x)) = _
  refine hc.symm.trans ?_
  change (AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.map f π ρ g h M U).f 0
    ((ModuleCat.extendScalars g.appTop.hom).map (φ.f 0)
      ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] x.val)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  refine (AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.one_tmul f π ρ g h M U 0 (φ.f 0 x.val)).trans ?_
  refine (congrArg (fun z ↦ (AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap f π ρ g h M U).f 0 z)
    (AlgebraicGeometry.Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.coordinate π M U hU φ x)).trans ?_
  exact CechSectionBaseChange.Construction.orderedCech_pullback_augmentation f π ρ g h M U _

include h hU φ in
theorem cechModel_sections_surjective_iff_cycles_lift :
    Function.Surjective (OpenPullbackSections.Construction.modulePullbackSection f M ⊤) ↔
      Function.Surjective (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle g.appTop.hom D) := by
  let e := AlgebraicGeometry.Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv π M U hU φ
  let eT := AlgebraicGeometry.Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections f π ρ g h M U hU φ
  let p : (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op ⊤) →
      (AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤) :=
    OpenPullbackSections.Construction.modulePullbackSection f M ⊤
  change Function.Surjective p ↔ Function.Surjective (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle g.appTop.hom D)
  exact (surjective_iff_of_equiv_square e.toEquiv eT.toEquiv
    (CochainBaseChangeCycles.Construction.cochainBaseChangeFirstCycle g.appTop.hom D) p
    (cechModel_sections_baseChange f π ρ g h M U hU φ)).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CechModelSectionCompatibility.Construction
