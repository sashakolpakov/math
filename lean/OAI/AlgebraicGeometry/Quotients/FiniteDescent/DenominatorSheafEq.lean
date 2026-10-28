import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorBase
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Flat.Localization

/-! # Denominator Sheaf Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorSheafEq.Construction.DenominatorSheaf

noncomputable section

/-! Denominator ideal data of a rational function on an integral scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X]

def affineIdeal (x : X.functionField) (U : X.affineOpens) : Ideal Γ(X, U) := by
  classical
  exact if h : Nonempty U.1 then
    let := h
    DenominatorIdealEq.Construction.DenominatorIdeal.ideal x
  else ⊤

theorem affineIdeal_eq (x : X.functionField) (U : X.affineOpens) [Nonempty U.1] :
    affineIdeal x U = DenominatorIdealEq.Construction.DenominatorIdeal.ideal (R := Γ(X, U)) x := by
  simp only [affineIdeal, dite_eq_left (inferInstance : Nonempty U.1)]

theorem scalarTower_restrict {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) :
    letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    IsScalarTower Γ(X, U) Γ(X, V) X.functionField := by
  let : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change X.germToFunctionField U r =
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op r)
  exact (X.presheaf.germ_res_apply (homOfLE h) (genericPoint X) _ r).symm

theorem map_affineIdeal_basicOpen (x : X.functionField) (U : X.affineOpens) (f : Γ(X, U)) :
    (affineIdeal x U).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      affineIdeal x (X.affineBasicOpen f) := by
  classical
  by_cases hV : Nonempty (X.basicOpen f)
  · have : Nonempty U.1 := ⟨⟨hV.some.1, X.basicOpen_le f hV.some.2⟩⟩
    have : Nonempty (X.basicOpen f) := hV
    have : Nonempty (X.affineBasicOpen f).1 := hV
    rw [affineIdeal_eq, affineIdeal_eq]
    let : Algebra Γ(X, U) Γ(X, X.basicOpen f) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    have := U.2.isLocalization_basicOpen f
    have : Module.Flat Γ(X, U) Γ(X, X.basicOpen f) :=
      IsLocalization.flat _ (Submonoid.powers f)
    have := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
    have := functionField_isFractionRing_of_isAffineOpen X (X.basicOpen f) (U.2.basicOpen f)
    have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) X.functionField :=
      scalarTower_restrict (X.basicOpen_le f)
    exact DenominatorBase.Construction.DenominatorBaseChange.map (R := Γ(X, U)) (S := Γ(X, X.basicOpen f))
      (F := X.functionField) x
  · have he : X.basicOpen f = ⊥ := by
      apply SetLike.ext
      intro y
      exact ⟨fun hy => (hV ⟨⟨y, hy⟩⟩).elim, fun hy => hy.elim⟩
    have : Subsingleton Γ(X, X.basicOpen f) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty he)
    exact Subsingleton.elim _ _

def data (x : X.functionField) : X.IdealSheafData where
  ideal := affineIdeal x
  map_ideal_basicOpen := map_affineIdeal_basicOpen x

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorSheafEq.Construction.DenominatorSheaf
