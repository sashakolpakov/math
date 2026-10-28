import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.ModuleTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalTotalNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.DoubleCechGlobalAugmentation

/-! # Regrouped -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Regrouped.Comparison

noncomputable section

/-! The actual global and local diagonal comparison maps agree on
cohomology after the canonical triple-total regrouping. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u r v
variable {C : Type u} [SemilatticeInf C]
  (R : Type r) [CommRing R] {ι : Type} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℕ)
  (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℕ)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

local notation "P" => B ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U
local notation "K" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U) Q

def diagonal := (GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map
  (LocalAugmentation.map U Q B γ h)

def global := DoubleCechGlobalAugmentation.map U P K
  (GlobalAugmentation.cone U Q B γ)

theorem diagonal_normalization : ModuleTotal.diagonal R U Q B γ h ≫
    DoubleCechRegrouping.map U P = diagonal R U Q B γ h :=
  DiagonalTotalNormalization.map_eq U Q B γ h

theorem global_normalization : ModuleTotal.global R U Q B γ ≫
    DoubleCechRegrouping.map U P = global R U Q B γ :=
  DoubleCechGlobalAugmentation.comparison U P K
    (GlobalAugmentation.cone U Q B γ)

private theorem postcomp_homology {D : Type*} [Category D] [Abelian D]
    {M L T : CochainComplex D ℕ} (f g : M ⟶ L) (a : L ⟶ T) (f' g' : M ⟶ T)
    (hf : f ≫ a = f') (hg : g ≫ a = g') (i : ℕ)
    (h : HomologicalComplex.homologyMap f i = HomologicalComplex.homologyMap g i) :
    HomologicalComplex.homologyMap f' i = HomologicalComplex.homologyMap g' i :=
  (congrArg (fun m => HomologicalComplex.homologyMap m i) hf.symm).trans
    ((HomologicalComplex.homologyMap_comp f a i).trans
      ((congrArg (fun m => m ≫ HomologicalComplex.homologyMap a i) h).trans
        ((HomologicalComplex.homologyMap_comp g a i).symm.trans
          (congrArg (fun m => HomologicalComplex.homologyMap m i) hg))))

abbrev homology (i : ℕ) := by
  have result := postcomp_homology
    (ModuleTotal.global R U Q B γ)
    (ModuleTotal.diagonal R U Q B γ h)
    (DoubleCechRegrouping.map U P) (global R U Q B γ) (diagonal R U Q B γ h)
    (global_normalization R U Q B γ) (diagonal_normalization R U Q B γ h) i
    (ModuleTotal.homology R U Q B γ h i).symm
  exact result

private theorem quasiIso_of_homology {D : Type*} [Category D] [Abelian D]
    {M L : CochainComplex D ℕ} (f g : M ⟶ L)
    (h : ∀ i, HomologicalComplex.homologyMap f i = HomologicalComplex.homologyMap g i)
    [hg : QuasiIso g] : QuasiIso f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, h i]
  exact (quasiIsoAt_iff_isIso_homologyMap g i).mp inferInstance

theorem global_quasiIso (hq : QuasiIso (diagonal R U Q B γ h)) :
    QuasiIso (global R U Q B γ) :=
  quasiIso_of_homology (global R U Q B γ) (diagonal R U Q B γ h) (homology R U Q B γ h) (hg := hq)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Regrouped.Comparison
