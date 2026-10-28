import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Left Exact Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LeftExactHomology.Comparison

noncomputable section

/-! Canonical comparison from homology of a left exact image to the image of homology. -/

open _root_.CategoryTheory Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (S : ShortComplex C)

def cyclesIso : (S.map F).cycles ≅ F.obj S.cycles :=
  ((S.map F).isoCyclesOfIsLimit (KernelFork.mapIsLimit _ S.cyclesIsKernel F)).symm

theorem cycles_i : (Comparison.cyclesIso F S).hom ≫ F.map S.iCycles = (S.map F).iCycles :=
  (S.map F).isoCyclesOfIsLimit_inv_ι (KernelFork.mapIsLimit _ S.cyclesIsKernel F)

theorem toCycles_map : (S.map F).toCycles ≫ (Comparison.cyclesIso F S).hom = F.map S.toCycles := by
  apply (cancel_mono (F.map S.iCycles)).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => (S.map F).toCycles ≫ a) (cycles_i F S)).trans
      ((S.map F).toCycles_i.trans
        ((congrArg F.map S.toCycles_i.symm).trans (F.map_comp _ _))))

def map : (S.map F).homology ⟶ F.obj S.homology :=
  (S.map F).descHomology ((Comparison.cyclesIso F S).hom ≫ F.map S.homologyπ) (by
    rw [← Category.assoc, toCycles_map]
    exact (F.map_comp S.toCycles S.homologyπ).symm.trans
      ((congrArg F.map S.toCycles_comp_homologyπ).trans (F.map_zero _ _)))

theorem π_map : (S.map F).homologyπ ≫ Comparison.map F S = (Comparison.cyclesIso F S).hom ≫ F.map S.homologyπ :=
  (S.map F).π_descHomology _ _

variable {S} {T : ShortComplex C}

theorem cycles_naturality (φ : S ⟶ T) :
    ShortComplex.cyclesMap (F.mapShortComplex.map φ) ≫ (Comparison.cyclesIso F T).hom =
      (Comparison.cyclesIso F S).hom ≫ F.map (ShortComplex.cyclesMap φ) := by
  let ψ : S.map F ⟶ T.map F := F.mapShortComplex.map φ
  change ShortComplex.cyclesMap ψ ≫ (Comparison.cyclesIso F T).hom = _
  apply (cancel_mono (F.map T.iCycles)).mp
  have hl := (Category.assoc (ShortComplex.cyclesMap ψ) (Comparison.cyclesIso F T).hom (F.map T.iCycles)).trans
    ((congrArg (fun a => ShortComplex.cyclesMap ψ ≫ a) (cycles_i F T)).trans
      (ShortComplex.cyclesMap_i ψ))
  have hr : ((Comparison.cyclesIso F S).hom ≫ F.map (ShortComplex.cyclesMap φ)) ≫ F.map T.iCycles =
      (S.map F).iCycles ≫ F.map φ.τ₂ := by
    rw [Category.assoc, ← F.map_comp, ShortComplex.cyclesMap_i, F.map_comp, ← Category.assoc, cycles_i]
  exact hl.trans hr.symm

theorem naturality (φ : S ⟶ T) :
    ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫ Comparison.map F T =
      Comparison.map F S ≫ F.map (ShortComplex.homologyMap φ) := by
  let ψ : S.map F ⟶ T.map F := F.mapShortComplex.map φ
  change ShortComplex.homologyMap ψ ≫ Comparison.map F T = _
  apply (cancel_epi (S.map F).homologyπ).mp
  calc
    _ = ((S.map F).homologyπ ≫ ShortComplex.homologyMap ψ) ≫ Comparison.map F T := (Category.assoc _ _ _).symm
    _ = (ShortComplex.cyclesMap ψ ≫ (T.map F).homologyπ) ≫ Comparison.map F T :=
      congrArg (fun a => a ≫ Comparison.map F T) (ShortComplex.homologyπ_naturality ψ)
    _ = (ShortComplex.cyclesMap ψ ≫ (Comparison.cyclesIso F T).hom) ≫ F.map T.homologyπ := by
      rw [Category.assoc, π_map, ← Category.assoc]
    _ = ((Comparison.cyclesIso F S).hom ≫ F.map (ShortComplex.cyclesMap φ)) ≫ F.map T.homologyπ :=
      congrArg (fun a => a ≫ F.map T.homologyπ) (cycles_naturality F φ)
    _ = (Comparison.cyclesIso F S).hom ≫ F.map (ShortComplex.cyclesMap φ ≫ T.homologyπ) := by
      rw [Category.assoc, F.map_comp]
    _ = (Comparison.cyclesIso F S).hom ≫ F.map (S.homologyπ ≫ ShortComplex.homologyMap φ) :=
      congrArg (fun a => (Comparison.cyclesIso F S).hom ≫ F.map a) (ShortComplex.homologyπ_naturality φ).symm
    _ = ((S.map F).homologyπ ≫ Comparison.map F S) ≫ F.map (ShortComplex.homologyMap φ) := by
      rw [F.map_comp, ← Category.assoc, π_map]
    _ = _ := Category.assoc _ _ _

variable (S)

theorem isIso [F.PreservesLeftHomologyOf S] : IsIso (Comparison.map F S) := by
  let h := (ShortComplex.LeftHomologyData.canonical S).map F
  have hcycles : (Comparison.cyclesIso F S).hom = h.cyclesIso.hom := by
    apply (cancel_mono (F.map S.iCycles)).mp
    exact (cycles_i F S).trans h.cyclesIso_hom_comp_i.symm
  have heq : Comparison.map F S = h.homologyIso.hom := by
    apply (cancel_epi (S.map F).homologyπ).mp
    exact (π_map F S).trans ((congrArg (fun a => a ≫ F.map S.homologyπ) hcycles).trans
      h.homologyπ_comp_homologyIso_hom.symm)
  rw [heq]
  exact h.homologyIso.isIso_hom

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LeftExactHomology.Comparison
