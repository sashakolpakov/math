import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions

/-! # Proper Product Line Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperProductLineUnits

noncomputable section

/-! A line automorphism on a proper integral product is a unit from the parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits

variable {k : Type u} [Field k] [IsAlgClosed k]
  (T A : Over (Spec (.of k))) [IsProper A.hom] [IsIntegral A.left]

/-- Properness makes the projection an isomorphism on global functions, for every parameter scheme. -/
def functionsIso : Γ(T.left, ⊤) ≅ Γ((T ⊗ A).left, ⊤) := by
  haveI : IsIso (fst T A).left.appTop :=
    PELModuli.IntegralModel.Picard.GlobalFunctions.PicardFunctions.isIso_properBaseChange_app T A ⊤
  exact asIso (fst T A).left.appTop

/-- The unique unit on the parameter scheme whose pullback is the given product unit. -/
def baseUnit (r : Γ((T ⊗ A).left, ⊤)ˣ) : Γ(T.left, ⊤)ˣ :=
  Units.map (functionsIso T A).inv.hom r

theorem pullback_baseUnit (r : Γ((T ⊗ A).left, ⊤)ˣ) :
    Units.map (fst T A).left.appTop.hom (baseUnit T A r) = r := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (functionsIso T A).inv_hom_id r.val

theorem baseUnit_pullback (r : Γ(T.left, ⊤)ˣ) :
    baseUnit T A (Units.map (fst T A).left.appTop.hom r) = r := by
  apply Units.ext
  exact ConcreteCategory.congr_hom (functionsIso T A).hom_inv_id r.val

theorem projection_units_injective :
    Function.Injective (Units.map (fst T A).left.appTop.hom.toMonoidHom) := by
  intro r s h
  exact (baseUnit_pullback T A r).symm.trans
    ((congrArg (baseUnit T A) h).trans (baseUnit_pullback T A s))

theorem existsUnique_baseUnit (r : Γ((T ⊗ A).left, ⊤)ˣ) :
    ∃! s : Γ(T.left, ⊤)ˣ, Units.map (fst T A).left.appTop.hom s = r := by
  refine ⟨baseUnit T A r, pullback_baseUnit T A r, ?_⟩
  intro s hs
  exact projection_units_injective T A (hs.trans (pullback_baseUnit T A r).symm)

variable {M : (T ⊗ A).left.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M)

/-- An arbitrary line-bundle automorphism on the product has a unique base coefficient. -/
def automorphismBaseUnit (e : M ≅ M) : Γ(T.left, ⊤)ˣ :=
  baseUnit T A (Line.AutomorphismUnits.unitOfAut hM e)

theorem automorphismBaseUnit_spec (e : M ≅ M) :
    Isogenies.NeighborCounting.ModuleScalar.scalarIso M (Units.map (fst T A).left.appTop.hom (automorphismBaseUnit T A hM e)) = e := by
  change Isogenies.NeighborCounting.ModuleScalar.scalarIso M (Units.map (fst T A).left.appTop.hom (baseUnit T A (Line.AutomorphismUnits.unitOfAut hM e))) = e
  rw [pullback_baseUnit, Line.AutomorphismUnits.scalarIso_unitOfAut]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperProductLineUnits
