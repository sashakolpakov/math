import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegerGeneratorPullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullbackIso

/-! # Pro Etale Pullback Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtalePullbackSections

noncomputable section

/-! Actual sections pull back through the inverse-image adjunction.
These formulas retain the native coefficient and constant-sheaf maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

abbrev adjunction := (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
  (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

def sectionMap (H : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    {U : X.ProEt} {V : Y.ProEt} (h : U ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj V) :
    H.obj.obj (op V) →+ ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H).obj.obj (op U) :=
  (((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H).obj.map h.op).hom.comp
    (((adjunction f).unit.app H).hom.app (op V)).hom

theorem transpose_section (H : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (Q : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (g : (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H ⟶ Q)
    {U : X.ProEt} {V : Y.ProEt} (h : U ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj V)
    (x : H.obj.obj (op V)) :
    g.hom.app (op U) (sectionMap f H h x) =
      Q.obj.map h.op (((adjunction f).homEquiv _ _ g).hom.app (op V) x) := by
  change g.hom.app (op U)
      (((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H).obj.map h.op
        (((adjunction f).unit.app H).hom.app (op V) x)) = _
  rw [NatTrans.naturality_apply, Adjunction.homEquiv_unit]
  rfl

theorem naturality {H Q : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} (α : H ⟶ Q)
    {U : X.ProEt} {V : Y.ProEt} (h : U ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj V)
    (x : H.obj.obj (op V)) :
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).map α).hom.app (op U) (sectionMap f H h x) =
      sectionMap f Q h (α.hom.app (op V) x) := by
  have he := (adjunction f).unit.naturality α
  have hx := congrArg (fun g : H ⟶
      ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).sheafPushforwardContinuous Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj Q) =>
    g.hom.app (op V) x) he
  change ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).map α).hom.app (op U)
      (((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H).obj.map h.op
        (((adjunction f).unit.app H).hom.app (op V) x)) = _
  rw [NatTrans.naturality_apply]
  exact congrArg (((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj Q).obj.map h.op) hx.symm

theorem restrict_source (H : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    {U U' : X.ProEt} {V : Y.ProEt} (h : U ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj V) (p : U' ⟶ U)
    (x : H.obj.obj (op V)) :
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H).obj.map p.op (sectionMap f H h x) =
      sectionMap f H (p ≫ h) x := by
  dsimp only [sectionMap, AddMonoidHom.comp_apply]
  rw [op_comp, CategoryTheory.Functor.map_comp]
  rfl

theorem restrict_target (H : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    {U : X.ProEt} {V V' : Y.ProEt} (h : U ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj V') (p : V' ⟶ V)
    (x : H.obj.obj (op V)) :
    sectionMap f H h (H.obj.map p.op x) =
      sectionMap f H (h ≫ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).map p) x := by
  have he := NatTrans.naturality_apply ((adjunction f).unit.app H).hom p.op x
  change ((adjunction f).unit.app H).hom.app (op V') (H.obj.map p.op x) =
    ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H).obj.map ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).map p).op
      (((adjunction f).unit.app H).hom.app (op V) x) at he
  change ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H).obj.map h.op
      (((adjunction f).unit.app H).hom.app (op V') (H.obj.map p.op x)) = _
  rw [he]
  change _ = ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj H).obj.map (h ≫ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).map p).op
    (((adjunction f).unit.app H).hom.app (op V) x)
  rw [op_comp, CategoryTheory.Functor.map_comp]
  rfl

theorem finite_coefficient (ℓ n : ℕ) [Fact ℓ.Prime]
    {U : X.ProEt} {V : Y.ProEt} (h : U ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj V)
    (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y).obj.obj (op V)) (z : U.left) :
    ULift.down (α := C(U.left, ZMod (ℓ ^ n)))
      ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f).hom.app (op U)
        (sectionMap f (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y) h x)) z =
      ULift.down (α := C(V.left, ZMod (ℓ ^ n))) x ((pullback.fst V.hom f) (h.left z)) := by
  rw [transpose_section]
  have he : (adjunction f).homEquiv _ _ (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f) =
      AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientToPushforward ℓ n f :=
    (adjunction f).homEquiv _ _ |>.apply_symm_apply _
  rw [he]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtalePullbackSections
