import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport

/-! # Cycles Exact Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.CyclesExactFunctor

noncomputable section

/-! Exact functors preserve the native cycle sequences used in the original Ext comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (K : CochainComplex C ℕ)

local notation "L" => Functor.obj (Functor.mapHomologicalComplex F (ComplexShape.up ℕ)) K

def cyclesIso (n : ℕ) : F.obj (ResolutionCycles.differentialSequence K n).cycles ≅ (ResolutionCycles.differentialSequence L n).cycles :=
  ((ResolutionCycles.differentialSequence K n).mapCyclesIso F).symm

theorem cycles_i (n : ℕ) : (cyclesIso F K n).hom ≫ (ResolutionCycles.differentialSequence L n).iCycles =
    F.map (ResolutionCycles.differentialSequence K n).iCycles := by
  have h := (ResolutionCycles.differentialSequence K n).mapCyclesIso_hom_iCycles F
  exact (congrArg (fun a => ((ResolutionCycles.differentialSequence K n).mapCyclesIso F).inv ≫ a) h).symm.trans
    (Iso.inv_hom_id_assoc _ _)

theorem toCycles (n : ℕ) : F.map (ResolutionCycles.differentialSequence K n).toCycles ≫ (cyclesIso F K n).hom =
    (ResolutionCycles.differentialSequence L n).toCycles := by
  apply (cancel_mono (ResolutionCycles.differentialSequence L n).iCycles).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => F.map (ResolutionCycles.differentialSequence K n).toCycles ≫ a) (cycles_i F K n)).trans
      ((F.map_comp (ResolutionCycles.differentialSequence K n).toCycles (ResolutionCycles.differentialSequence K n).iCycles).symm.trans
        ((congrArg F.map (ResolutionCycles.differentialSequence K n).toCycles_i).trans
          (ResolutionCycles.differentialSequence L n).toCycles_i.symm)))

variable {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ D).obj (F.obj Z) ⟶
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (hκ : κ.f 0 = F.map (ι.f 0))

def initialIso : (ResolutionCycles.initialSequence K ι).map F ≅ ResolutionCycles.initialSequence L κ :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (cyclesIso F K 0)
    ((Category.id_comp _).trans (hκ.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans (CyclesExactFunctor.toCycles F K 0).symm)

def successiveIso (n : ℕ) : (ResolutionCycles.successiveSequence K n).map F ≅ ResolutionCycles.successiveSequence L n :=
  ShortComplex.isoMk (cyclesIso F K n) (Iso.refl _) (cyclesIso F K (n + 1))
    ((cycles_i F K n).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (CyclesExactFunctor.toCycles F K (n + 1)).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.CyclesExactFunctor
