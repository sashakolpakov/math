import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FreeDualBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.FlatBaseChange
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Dual Flat Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualFlatBaseChange

noncomputable section

/-! Flat scalar extension of the actual dual exterior Koszul complex,
normalized by its ordered basis wedge. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def dualIso {ι : Type v} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (e : K ≅ L) :
    DualComplexHomology.complex R K ≅ DualComplexHomology.complex R L :=
  ((DualComplexHomology.dual R).mapHomologicalComplex c.symm).mapIso
    ((HomologicalComplex.opFunctor (ModuleCat.{u} R) c).mapIso e.op.symm)

variable (V : Type u) [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]
  (s : Module.Dual R V) [Module.Flat R S]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulComplex OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.ContractionBaseChange

abbrev tensorFunctor := FlatBaseChange.tensorFunctor R S

def iso : ((tensorFunctor R S).mapHomologicalComplex (.up ℕ)).obj
        (DualComplexHomology.complex R (Exterior.KoszulComplex.complex R V s)) ≅
    DualComplexHomology.complex S
      (Exterior.KoszulComplex.complex S (S ⊗[R] V) (Exterior.ContractionBaseChange.coefficient R S V s)) := by
  letI (i : ℕ) : Module.Free R ((Exterior.KoszulComplex.complex R V s).X i) :=
    inferInstanceAs (Module.Free R (⋀[R]^i V))
  letI (i : ℕ) : Module.Finite R ((Exterior.KoszulComplex.complex R V s).X i) :=
    inferInstanceAs (Module.Finite R (⋀[R]^i V))
  exact IntegralComparison.Finite.FreeDualBaseChange.complexIso R S (Exterior.KoszulComplex.complex R V s) ≪≫
    dualIso S (FlatBaseChange.iso R S V s)

def component (n : ℕ) : S ⊗[R] Module.Dual R (⋀[R]^n V) →ₗ[S]
    Module.Dual S (⋀[S]^n (S ⊗[R] V)) :=
  ((iso R S V s).hom.f n).hom

theorem iso_top_evaluation {n : ℕ} (b : Module.Basis (Fin n) R V)
    (a : S) (f : Module.Dual R (⋀[R]^n V)) :
    component R S V s n (a ⊗ₜ[R] f)
        (TopExteriorCoordinates.generator (b.baseChange S)) =
      a * algebraMap R S (f (TopExteriorCoordinates.generator b)) := by
  change IntegralComparison.Finite.FreeDualBaseChange.equiv R S (⋀[R]^n V) (a ⊗ₜ[R] f)
      ((Exterior.ContractionBaseChange.power R S V n).symm (TopExteriorCoordinates.generator (b.baseChange S))) = _
  have h : (Exterior.ContractionBaseChange.power R S V n).symm
      (TopExteriorCoordinates.generator (b.baseChange S)) =
        1 ⊗ₜ[R] TopExteriorCoordinates.generator b := by
    apply (Exterior.ContractionBaseChange.power R S V n).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (FlatBaseChange.iso_top_generator R S V s b).symm
  rw [h, IntegralComparison.Finite.FreeDualBaseChange.equiv_tmul_one]

def homologyIso (n : ℕ) :
    (tensorFunctor R S).obj ((DualComplexHomology.complex R (Exterior.KoszulComplex.complex R V s)).homology n) ≅
      (DualComplexHomology.complex S
        (Exterior.KoszulComplex.complex S (S ⊗[R] V) (Exterior.ContractionBaseChange.coefficient R S V s))).homology n :=
  (((DualComplexHomology.complex R (Exterior.KoszulComplex.complex R V s)).sc n).mapHomologyIso
      (tensorFunctor R S)).symm ≪≫ homologyMapIso (iso R S V s) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DualFlatBaseChange
