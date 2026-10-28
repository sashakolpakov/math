import Mathlib

/-! # Sheaf Resolution Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafResolutionSections

noncomputable section

/-!
# IntegralComparison: vanishing Ext makes sections of an injective resolution exact

The original constant module sheaf represents sections at a terminal
object. A cycle in sections therefore defines an actual Ext class;
vanishing of that class supplies a boundary in the same resolution.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe w w' u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type w) [Ring R] [HasSheafify J (ModuleCat.{w} R)]
  {T : C} (hT : IsTerminal T)

abbrev constantUnit : Sheaf J (ModuleCat.{w} R) :=
  (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)

def homEquiv (M : Sheaf J (ModuleCat.{w} R)) :
    (constantUnit J R ⟶ M) ≃+ M.obj.obj (op T) :=
  ((constantSheafAdj J (ModuleCat.{w} R) hT).homAddEquiv (ModuleCat.of R R) M).trans
    (ModuleCat.homAddEquiv.trans (LinearMap.ringLmapEquivSelf R ℤ _).toAddEquiv)

theorem homEquiv_natural {M N : Sheaf J (ModuleCat.{w} R)}
    (a : constantUnit J R ⟶ M) (b : M ⟶ N) :
    SheafResolutionSections.homEquiv J R hT N (a ≫ b) = b.hom.app (op T) (SheafResolutionSections.homEquiv J R hT M a) := by
  change (((constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv _ N) (a ≫ b)).hom 1 = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

variable [HasExt.{w'} (Sheaf J (ModuleCat.{w} R))]
  {M : Sheaf J (ModuleCat.{w} R)} (I : InjectiveResolution M)

include hT in
theorem exact_succ (n : ℕ) [Subsingleton (Abelian.Ext.{w'} (constantUnit J R) M (n + 1))]
    (x : (I.cocomplex.X (n + 1)).obj.obj (op T))
    (hx : (I.cocomplex.d (n + 1) (n + 2)).hom.app (op T) x = 0) :
    ∃ y : (I.cocomplex.X n).obj.obj (op T),
      (I.cocomplex.d n (n + 1)).hom.app (op T) y = x := by
  let a := (SheafResolutionSections.homEquiv J R hT (I.cocomplex.X (n + 1))).symm x
  have ha : a ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
    apply (SheafResolutionSections.homEquiv J R hT _).injective
    rw [homEquiv_natural, AddEquiv.map_zero]
    exact (congrArg ((I.cocomplex.d (n + 1) (n + 2)).hom.app (op T))
      ((SheafResolutionSections.homEquiv J R hT _).apply_symm_apply x)).trans hx
  obtain ⟨b, hb⟩ := (I.extMk_eq_zero_iff a (n + 2) rfl ha n rfl).mp (Subsingleton.elim _ _)
  refine ⟨SheafResolutionSections.homEquiv J R hT _ b, ?_⟩
  rw [← homEquiv_natural, hb]
  exact (SheafResolutionSections.homEquiv J R hT _).apply_symm_apply x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafResolutionSections
