import OAI.NumberTheory.PadicHodge.PeriodInvariants.ProEtaleCoherence

/-! # Constant Sheaf Coherence -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence

noncomputable section

/-!
# The canonical generators of transported constant sheaves

A constant sheaf is the sheafification of the constant presheaf. The canonical
transport isomorphism preserves its generating maps. This characterizes the
isomorphism independently of choices of terminal objects.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

section Generators

variable {C A : Type*} [Category C] [Category A]
variable (J : GrothendieckTopology C) [HasWeakSheafify J A]

def constantGenerator (a : A) : (Functor.const Cᵒᵖ).obj a ⟶ ((constantSheaf J A).obj a).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj a)

theorem constantGenerator_naturality (a : A) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (constantGenerator J a).app U ≫ ((constantSheaf J A).obj a).obj.map f =
      (constantGenerator J a).app V := by
  have h := (constantGenerator J a).naturality f
  exact h.symm.trans (Category.id_comp _)

theorem constantAdj_unit_app {T : C} (hT : IsTerminal T) (a : A) :
    (constantSheafAdj J A hT).unit.app a = (constantGenerator J a).app (op T) := by
  rw [constantSheafAdj, Adjunction.comp_unit_app]
  change (𝟙 a) ≫ (constantGenerator J a).app (op T) = _
  exact Category.id_comp _

theorem fromConstant_ext {T : C} (hT : IsTerminal T) {a : A} {F : Cᵒᵖ ⥤ A}
    (α β : (Functor.const Cᵒᵖ).obj a ⟶ F) (h : α.app (op T) = β.app (op T)) : α = β := by
  apply NatTrans.ext
  funext U
  have ha := α.naturality (hT.from U.unop).op
  have hb := β.naturality (hT.from U.unop).op
  exact (Category.id_comp _).symm.trans (ha.trans
    ((congrArg (fun f => f ≫ F.map (hT.from U.unop).op) h).trans
      (hb.symm.trans (Category.id_comp _))))

theorem constant_hom_ext {a : A} {F : Sheaf J A}
    (α β : (constantSheaf J A).obj a ⟶ F)
    (h : constantGenerator J a ≫ α.hom = constantGenerator J a ≫ β.hom) : α = β := by
  apply Sheaf.hom_ext
  exact sheafify_hom_ext J α.hom β.hom F.property h

end Generators

open OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale

variable (A : Type*) [Category A]
variable {X Y : Scheme.{u}} (e : X ≅ Y)
variable [HasWeakSheafify (Scheme.ProEt.topology X) A]
  [HasWeakSheafify (Scheme.ProEt.topology Y) A]

def transportedConstantGenerator (a : A) :
    (Functor.const Y.ProEtᵒᵖ).obj a ⟶
      ((IntegralComparison.ProEtale.proEtaleSheafCongr A e).functor.obj ((constantSheaf (Scheme.ProEt.topology X) A).obj a)).obj :=
  whiskerLeft (IntegralComparison.ProEtale.proEtaleCongr e).inverse.op (constantGenerator (Scheme.ProEt.topology X) a)

/-- The actual constant-sheaf transport isomorphism preserves the canonical generating maps. -/
theorem constantTransport_generators (a : A) :
    transportedConstantGenerator A e a ≫ ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant A e).hom.app a).hom =
      constantGenerator (Scheme.ProEt.topology Y) a := by
  let E := IntegralComparison.ProEtale.proEtaleSheafCongr A e
  let T := (IntegralComparison.ProEtale.proEtaleCongr e).functor.obj (⊤_ X.ProEt)
  have hT : IsTerminal T := terminalIsTerminal.isTerminalObj (IntegralComparison.ProEtale.proEtaleCongr e).functor (⊤_ X.ProEt)
  apply fromConstant_ext hT
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((constantSheafAdj (Scheme.ProEt.topology X) A
      (terminalIsTerminal : IsTerminal (⊤_ X.ProEt))).comp E.toAdjunction)
    (constantSheafAdj (Scheme.ProEt.topology Y) A hT) a
  rw [Adjunction.comp_unit_app, constantAdj_unit_app, constantAdj_unit_app] at h
  have hu : (constantGenerator (Scheme.ProEt.topology X) a).app (op (⊤_ X.ProEt)) ≫
      ((E.unitIso.hom.app ((constantSheaf (Scheme.ProEt.topology X) A).obj a)).hom.app
        (op (⊤_ X.ProEt))) = (transportedConstantGenerator A e a).app (op T) := by
    exact constantGenerator_naturality (Scheme.ProEt.topology X) a
      ((IntegralComparison.ProEtale.proEtaleCongr e).op.unitIso.hom.app (op (⊤_ X.ProEt)))
  change ((constantGenerator (Scheme.ProEt.topology X) a).app (op (⊤_ X.ProEt)) ≫
      ((E.unitIso.hom.app ((constantSheaf (Scheme.ProEt.topology X) A).obj a)).hom.app
        (op (⊤_ X.ProEt)))) ≫
      (((IntegralComparison.ProEtale.proEtaleSheafCongr_constant A e).hom.app a).hom.app (op T)) =
    (constantGenerator (Scheme.ProEt.topology Y) a).app (op T) at h
  rw [hu] at h
  exact h

theorem transportedConstant_hom_ext {a : A} {F : Sheaf (Scheme.ProEt.topology Y) A}
    (α β : (IntegralComparison.ProEtale.proEtaleSheafCongr A e).functor.obj
      ((constantSheaf (Scheme.ProEt.topology X) A).obj a) ⟶ F)
    (h : transportedConstantGenerator A e a ≫ α.hom =
      transportedConstantGenerator A e a ≫ β.hom) : α = β := by
  let c := (sheafToPresheaf (Scheme.ProEt.topology Y) A).mapIso
    ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant A e).app a)
  have hc : transportedConstantGenerator A e a ≫ c.hom =
      constantGenerator (Scheme.ProEt.topology Y) a := constantTransport_generators A e a
  have hg : constantGenerator (Scheme.ProEt.topology Y) a ≫ c.inv =
      transportedConstantGenerator A e a := by
    exact (congrArg (fun z => z ≫ c.inv) hc).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => transportedConstantGenerator A e a ≫ z) c.hom_inv_id).trans
          (Category.comp_id _)))
  apply Sheaf.hom_ext
  apply (cancel_epi c.inv).mp
  apply sheafify_hom_ext (Scheme.ProEt.topology Y) _ _ F.property
  exact (Category.assoc (constantGenerator (Scheme.ProEt.topology Y) a) c.inv α.hom).symm.trans
    ((congrArg (fun z => z ≫ α.hom) hg).trans
      (h.trans ((congrArg (fun z => z ≫ β.hom) hg).symm.trans
        (Category.assoc _ _ _))))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantSheafCoherence
