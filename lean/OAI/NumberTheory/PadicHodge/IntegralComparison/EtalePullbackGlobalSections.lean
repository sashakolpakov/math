import OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtalePullbackSections

/-! # Etale Pullback Global Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtalePullbackGlobalSections.Pro

noncomputable section

/-! Pullback of global sections agrees with the native degree-zero Ext
transport, including the constructed integer constant comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtalePullbackSections

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def terminalMap : (⊤_ X.ProEt) ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj (⊤_ Y.ProEt) :=
  (terminalIsTerminal.isTerminalObj (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f) (⊤_ Y.ProEt)).from _

def globalMap (H : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :
    H.obj.obj (op (⊤_ Y.ProEt)) →+
      ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H).obj.obj (op (⊤_ X.ProEt)) :=
  ProEtalePullbackSections.sectionMap f H (terminalMap f)

theorem local_global (H : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    {U : X.ProEt} {V : Y.ProEt} (h : U ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj V)
    (z : H.obj.obj (op (⊤_ Y.ProEt))) :
    ProEtalePullbackSections.sectionMap f H h (H.obj.map (terminal.from V).op z) =
      ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H).obj.map (terminal.from U).op (globalMap f H z) := by
  rw [ProEtalePullbackSections.restrict_target, globalMap, ProEtalePullbackSections.restrict_source]
  exact congrArg (fun h => ProEtalePullbackSections.sectionMap f H h z)
    ((terminalIsTerminal.isTerminalObj (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f) (⊤_ Y.ProEt)).hom_ext _ _)

theorem integer_generator {U : X.ProEt} {V : Y.ProEt}
    (h : U ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj V) :
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso f).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom.app (op U)
      (ProEtalePullbackSections.sectionMap f (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant Y) h (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator Y V)) =
        AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X U := by
  have he := ProEtalePullbackSections.transpose_section f (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant Y) (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X)
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso f).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    h (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator Y V)
  rw [AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence.Construction.proEtConstantPullbackIso_adjoint,
    AlgebraicGeometry.FormalGeometry.Completion.IntegerGeneratorPullback.Construction.proEtConstantToPushforward_integerGenerator, AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator_naturality] at he
  exact he

theorem equiv₀_mk₀ (H : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (a : AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X ⟶ H) :
    Sheaf.H.equiv₀ H terminalIsTerminal (Ext.mk₀ a) =
      a.hom.app (op (⊤_ X.ProEt)) (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerGenerator X) := by
  rw [AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerGenerator, Sheaf.H.equiv₀_naturality]
  change _ = Sheaf.H.equiv₀ H terminalIsTerminal
    ((Ext.mk₀ (𝟙 _)).comp (Ext.mk₀ a) (add_zero 0))
  rw [Ext.mk₀_id_comp]

theorem equiv₀_global (H : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (z : H.obj.obj (op (⊤_ Y.ProEt))) :
    (Sheaf.H.equiv₀ ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H) terminalIsTerminal).symm (globalMap f H z) =
      (Ext.mk₀ ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).comp
        (((Sheaf.H.equiv₀ H terminalIsTerminal).symm z).mapExactFunctor (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f))
          (zero_add 0) := by
  obtain ⟨a, ha⟩ := (Ext.mk₀_bijective (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant Y) H).surjective
    ((Sheaf.H.equiv₀ H terminalIsTerminal).symm z)
  have hz : a.hom.app (op (⊤_ Y.ProEt)) (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerGenerator Y) = z := by
    rw [← equiv₀_mk₀, ha, AddEquiv.apply_symm_apply]
  apply (Sheaf.H.equiv₀ ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H) terminalIsTerminal).injective
  rw [AddEquiv.apply_symm_apply, ← ha, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, equiv₀_mk₀]
  rw [← hz]
  change ProEtalePullbackSections.sectionMap f H (terminalMap f)
      (a.hom.app (op (⊤_ Y.ProEt)) (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerGenerator Y)) = _
  rw [← ProEtalePullbackSections.naturality]
  have hgen := integer_generator f (terminalMap f)
  have hgy : AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator Y (⊤_ Y.ProEt) = AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerGenerator Y := by
    rw [AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator, show terminal.from (⊤_ Y.ProEt) = 𝟙 _ from Subsingleton.elim _ _]
    simp only [op_id,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  have hgx : AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X (⊤_ X.ProEt) = AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerGenerator X := by
    rw [AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator, show terminal.from (⊤_ X.ProEt) = 𝟙 _ from Subsingleton.elim _ _]
    simp only [op_id,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  rw [hgy, hgx] at hgen
  have hpre : ProEtalePullbackSections.sectionMap f (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant Y) (terminalMap f) (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerGenerator Y) =
      ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom.app
        (op (⊤_ X.ProEt)) (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerGenerator X) := by
    rw [← hgen]
    exact ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapIso
      ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtConstantPullbackIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).hom_inv_id_app_apply _ _ |>.symm
  rw [hpre]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtalePullbackGlobalSections.Pro
