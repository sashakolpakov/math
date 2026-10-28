import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Limit Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LimitBaseChange

noncomputable section

/-! A connected inverse limit over a fixed base remains the actual
scheme limit after arbitrary change of that base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {I : Type u} [Category.{u} I] [IsConnected I]
    {S X : Scheme.{u}} (f : X ⟶ S) {D : I ⥤ Over S} (c : Cone D)

def baseChangedSchemeCone : Cone (D ⋙ Over.pullback f ⋙ Over.forget X) :=
  (Over.forget X).mapCone ((Over.pullback f).mapCone c)

def baseChangedSchemeCone_isLimit (hc : IsLimit ((Over.forget S).mapCone c)) :
    IsLimit (baseChangedSchemeCone f c) :=
  isLimitOfPreserves (Over.forget X)
    (isLimitOfPreserves (Over.pullback f) (isLimitOfReflects (Over.forget S) hc))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LimitBaseChange
