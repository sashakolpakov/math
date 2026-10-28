import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.UnitCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FunctionsBaseChange

/-! # Unit Pullback Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.UnitPullbackReduction

noncomputable section

/-! Original units computed on open subschemes commute with arbitrary
scheme pullback. Equal reduced open maps therefore give equal reduced
units, including for nonflat infinitesimal reductions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem openUnitToRegular_pullback {X Y : Scheme.{0}} (r : X ⟶ Y) (U : Y.Opens)
    (u : Γ(U.toScheme, ⊤)ˣ) :
    Units.map (r.app U).hom.toMonoidHom (UnitCoordinates.openUnitToRegular U u) =
      UnitCoordinates.openUnitToRegular (r ⁻¹ᵁ U) (Units.map (r ∣_ U).appTop.hom.toMonoidHom u) := by
  apply Units.ext
  exact (ConcreteCategory.congr_hom (HilbertConstruction.Open.FunctionsBaseChange.morphismRestrict_appTop_topIso r U) u.val).symm

theorem openUnitToRegular_pullback_comp {X Y Z : Scheme.{0}} (r : X ⟶ Y)
    (U : Y.Opens) (p : U.toScheme ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    Units.map (r.app U).hom.toMonoidHom
      (UnitCoordinates.openUnitToRegular U (Units.map p.appTop.hom.toMonoidHom u)) =
    UnitCoordinates.openUnitToRegular (r ⁻¹ᵁ U) (Units.map ((r ∣_ U) ≫ p).appTop.hom.toMonoidHom u) := by
  rw [openUnitToRegular_pullback]
  apply congrArg (UnitCoordinates.openUnitToRegular (r ⁻¹ᵁ U))
  apply Units.ext
  exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop (r ∣_ U) p) u.val).symm

theorem openUnitToRegular_equal_reduction {X Y Z : Scheme.{0}} (r : X ⟶ Y)
    (U : Y.Opens) (p q : U.toScheme ⟶ Z) (h : (r ∣_ U) ≫ p = (r ∣_ U) ≫ q)
    (u : Γ(Z, ⊤)ˣ) :
    Units.map (r.app U).hom.toMonoidHom
      (UnitCoordinates.openUnitToRegular U (Units.map p.appTop.hom.toMonoidHom u)) =
    Units.map (r.app U).hom.toMonoidHom
      (UnitCoordinates.openUnitToRegular U (Units.map q.appTop.hom.toMonoidHom u)) := by
  rw [openUnitToRegular_pullback_comp, openUnitToRegular_pullback_comp, h]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.UnitPullbackReduction
