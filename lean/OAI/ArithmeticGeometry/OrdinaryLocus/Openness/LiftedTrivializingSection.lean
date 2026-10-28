import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleProperTriviality

/-! # Lifted Trivializing Section -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LiftedTrivializingSection.Construction

noncomputable section

/-! A lifted trivializing section produces a morphism that is invertible on the specified fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

theorem modulePullbackGlobalSection_one :
    PullbackModuleSections.Construction.modulePullbackGlobalSection f (LineBundle.Construction.structureSheafModule Y) (1 : Γ(Y, ⊤)) =
      (LineBundle.Construction.pullbackStructureSheafIso f).inv.app ⊤ (1 : Γ(X, ⊤)) := by
  apply (ConcreteCategory.bijective_of_isIso ((LineBundle.Construction.pullbackStructureSheafIso f).hom.app ⊤)).injective
  have h₁ : f.appTop (1 : Γ(Y, ⊤)) = (1 : Γ(X, ⊤)) := f.appTop.hom.map_one
  have h₂ := congrArg (fun q : LineBundle.Construction.structureSheafModule X ⟶ LineBundle.Construction.structureSheafModule X ↦
    q.app ⊤ (1 : Γ(X, ⊤))) (LineBundle.Construction.pullbackStructureSheafIso f).inv_hom_id
  exact (PullbackModuleSections.Construction.modulePullbackGlobalSection_unit f 1).trans (h₁.trans h₂.symm)

theorem structureSheafHomEquiv_pullback (q : LineBundle.Construction.structureSheafModule Y ⟶ M) :
    ModuleSections.Construction.structureSheafHomEquiv ((Scheme.Modules.pullback f).obj M)
      ((LineBundle.Construction.pullbackStructureSheafIso f).inv ≫ (Scheme.Modules.pullback f).map q) =
      PullbackModuleSections.Construction.modulePullbackGlobalSection f M (ModuleSections.Construction.structureSheafHomEquiv M q) := by
  have h := PullbackModuleSections.Construction.modulePullbackGlobalSection_naturality f q (1 : Γ(Y, ⊤))
  rw [modulePullbackGlobalSection_one] at h
  exact h

theorem exists_isIso_pullback_of_sections_surjective
    (e : (Scheme.Modules.pullback f).obj M ≅ LineBundle.Construction.structureSheafModule X)
    (hs : Function.Surjective (PullbackModuleSections.Construction.modulePullbackGlobalSection f M)) :
    ∃ q : LineBundle.Construction.structureSheafModule Y ⟶ M, IsIso ((Scheme.Modules.pullback f).map q) := by
  obtain ⟨m, hm⟩ := hs (ModuleSections.Construction.structureSheafHomEquiv ((Scheme.Modules.pullback f).obj M) e.inv)
  let q := (ModuleSections.Construction.structureSheafHomEquiv M).symm m
  have hq : (LineBundle.Construction.pullbackStructureSheafIso f).inv ≫ (Scheme.Modules.pullback f).map q = e.inv := by
    apply (ModuleSections.Construction.structureSheafHomEquiv ((Scheme.Modules.pullback f).obj M)).injective
    rw [structureSheafHomEquiv_pullback]
    change PullbackModuleSections.Construction.modulePullbackGlobalSection f M ((ModuleSections.Construction.structureSheafHomEquiv M) ((ModuleSections.Construction.structureSheafHomEquiv M).symm m)) = _
    rw [Equiv.apply_symm_apply]
    exact hm
  have hIso : IsIso ((LineBundle.Construction.pullbackStructureSheafIso f).inv ≫ (Scheme.Modules.pullback f).map q) := by
    rw [hq]
    infer_instance
  exact ⟨q, IsIso.of_isIso_comp_left (LineBundle.Construction.pullbackStructureSheafIso f).inv ((Scheme.Modules.pullback f).map q)⟩

theorem lineBundle_trivial_near_fiber_of_sections_surjective
    {T B : Scheme.{u}} (π : T ⟶ B) [UniversallyClosed π]
    (L : T.Modules) (hL : LineBundle.Construction.IsLineBundle L) (b : B)
    (e : (Scheme.Modules.pullback (π.fiberι b)).obj L ≅ LineBundle.Construction.structureSheafModule (π.fiber b))
    (hs : Function.Surjective (PullbackModuleSections.Construction.modulePullbackGlobalSection (π.fiberι b) L)) :
    ∃ W : B.Opens, b ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj L ≅ LineBundle.Construction.structureSheafModule (π ⁻¹ᵁ W).toScheme) := by
  obtain ⟨q, hq⟩ := exists_isIso_pullback_of_sections_surjective (π.fiberι b) L e hs
  exact LineBundleProperTriviality.Construction.lineBundle_trivial_near_fiber_of_global_section π L hL q b

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LiftedTrivializingSection.Construction
