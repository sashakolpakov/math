import OAI.NumberTheory.PadicHodge.PeriodInvariants.DegreeZeroSections
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Terminal Section Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TerminalSectionRestriction

noncomputable section

/-! Actual terminal sections and degree-zero Ext under restriction of sites. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian Opposite

universe u v u' v' w z z'

open OAI.NumberTheory.PadicHodge.PeriodInvariants.DegreeZeroSections OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (R : Type w) [CommRing R]
  [HasSheafify J (ModuleCat.{w} R)] [HasSheafify K (ModuleCat.{w} R)]
  {T : C} (hT : IsTerminal T) {S : D} (hS : IsTerminal S)

theorem generator_value (M : Sheaf K (ModuleCat.{w} R))
    (a : (constantSheaf K (ModuleCat.{w} R)).obj (ModuleCat.of R R) ⟶ M) :
    PeriodInvariants.DegreeZeroSections.homSectionsLinearEquiv K R hS M a =
      a.hom.app (op S) ((PeriodInvariants.ConstantSheafCoherence.constantGenerator K (ModuleCat.of R R)).app (op S) (1 : R)) := by
  change PeriodInvariants.DegreeZeroSections.homSectionsEquiv K R hS M a = _
  rw [PeriodInvariants.DegreeZeroSections.homSectionsEquiv_apply, Adjunction.homEquiv_unit, PeriodInvariants.ConstantSheafCoherence.constantAdj_unit_app]
  rfl

theorem generator_restrict (M : Sheaf K (ModuleCat.{w} R))
    (a : (constantSheaf K (ModuleCat.{w} R)).obj (ModuleCat.of R R) ⟶ M) (U : D) :
    a.hom.app (op U) ((PeriodInvariants.ConstantSheafCoherence.constantGenerator K (ModuleCat.of R R)).app (op U) (1 : R)) =
      M.obj.map (hS.from U).op (PeriodInvariants.DegreeZeroSections.homSectionsLinearEquiv K R hS M a) := by
  rw [generator_value]
  have h := PeriodInvariants.ConstantSheafCoherence.constantGenerator_naturality K (ModuleCat.of R R) (hS.from U).op
  have hn := a.hom.naturality (hS.from U).op
  have he := (congrArg (fun b => b ≫ a.hom.app (op U)) h).symm.trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun b => (PeriodInvariants.ConstantSheafCoherence.constantGenerator K (ModuleCat.of R R)).app (op S) ≫ b) hn))
  exact congrArg (fun b => b (1 : R)) he

variable (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  [∀ P : Cᵒᵖ ⥤ ModuleCat.{w} R, F.op.HasPointwiseRightKanExtension P]

abbrev restriction : Sheaf K (ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{w} R) :=
  F.sheafPushforwardContinuous (ModuleCat.{w} R) J K

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.TerminalSectionRestriction.restriction J K R F
local notation "c" => OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence.transport J K F (ModuleCat.of R R)

theorem hom (M : Sheaf K (ModuleCat.{w} R))
    (a : (constantSheaf K (ModuleCat.{w} R)).obj (ModuleCat.of R R) ⟶ M) :
    PeriodInvariants.DegreeZeroSections.homSectionsLinearEquiv J R hT ((G).obj M) ((c).inv ≫ (G).map a) =
      M.obj.map (hS.from (F.obj T)).op (PeriodInvariants.DegreeZeroSections.homSectionsLinearEquiv K R hS M a) := by
  rw [generator_value]
  have hg := congrArg (fun b => (b.app (op T)) (1 : R))
    (PeriodInvariants.ConstantRestrictionCoherence.transport_generator J K F (ModuleCat.of R R))
  change (c).inv.hom.app (op T)
      ((PeriodInvariants.ConstantSheafCoherence.constantGenerator J (ModuleCat.of R R)).app (op T) (1 : R)) =
    (PeriodInvariants.ConstantSheafCoherence.constantGenerator K (ModuleCat.of R R)).app (op (F.obj T)) (1 : R) at hg
  exact (congrArg (a.hom.app (op (F.obj T))) hg).trans
    (generator_restrict K R hS M a (F.obj T))

variable [HasExt.{z} (Sheaf K (ModuleCat.{w} R))]
  [HasExt.{z'} (Sheaf J (ModuleCat.{w} R))]
  [Functor.Additive (F.sheafPushforwardContinuous (ModuleCat.{w} R) J K)]
  [PreservesFiniteLimits (F.sheafPushforwardContinuous (ModuleCat.{w} R) J K)]
  [PreservesFiniteColimits (F.sheafPushforwardContinuous (ModuleCat.{w} R) J K)]

theorem cohomology (M : Sheaf K (ModuleCat.{w} R))
    (x : Ext ((constantSheaf K (ModuleCat.{w} R)).obj (ModuleCat.of R R)) M 0) :
    PeriodInvariants.DegreeZeroSections.degreeZeroEquiv J R hT ((G).obj M)
        ((Ext.mk₀ (c).inv).comp (x.mapExactFunctor G) (Nat.zero_add 0)) =
      M.obj.map (hS.from (F.obj T)).op (PeriodInvariants.DegreeZeroSections.degreeZeroEquiv K R hS M x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  change PeriodInvariants.DegreeZeroSections.homSectionsLinearEquiv J R hT ((G).obj M) (Ext.linearEquiv₀ (Ext.mk₀ _)) =
    M.obj.map (hS.from (F.obj T)).op
      (PeriodInvariants.DegreeZeroSections.homSectionsLinearEquiv K R hS M (Ext.linearEquiv₀ (Ext.mk₀ a)))
  exact (congrArg (PeriodInvariants.DegreeZeroSections.homSectionsLinearEquiv J R hT ((G).obj M))
    ((Ext.linearEquiv₀ (R := R)).apply_symm_apply ((c).inv ≫ (G).map a))).trans
      ((TerminalSectionRestriction.hom J K R hT hS F M a).trans
        (congrArg (fun b => M.obj.map (hS.from (F.obj T)).op (PeriodInvariants.DegreeZeroSections.homSectionsLinearEquiv K R hS M b))
          ((Ext.linearEquiv₀ (R := R)).apply_symm_apply a).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TerminalSectionRestriction
