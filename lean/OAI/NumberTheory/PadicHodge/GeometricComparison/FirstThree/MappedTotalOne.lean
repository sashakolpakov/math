import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Mapped Total One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotalOne.FirstThreeMappedTotalHOne

noncomputable section

/-! Retaining form degrees zero through two preserves H-one of the original
first-quadrant total after an additive row functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a b
variable (R : Type u) [CommRing R]
  {C : Type a} [Category.{b} C] [Preadditive C] [HasZeroObject C]
  (G : C ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ) [G.Additive]
  (K : CochainComplex C ℕ)

def bicomplexMap := (G.mapHomologicalComplex (.up ℕ)).map (ThreeComplex.FirstThreeComplex.projection K)

theorem row_isIso (q : ℕ) (hq : q ≤ 2) : IsIso ((bicomplexMap R G K).f q) := by
  have h : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases h with rfl | rfl | rfl
  all_goals
    change IsIso (G.map (𝟙 _))
    infer_instance

local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v, u, 0, 0} R

def map := HomologicalComplex₂.total.map (bicomplexMap R G K) (.up ℕ)

theorem quasiIsoAt : QuasiIsoAt (FirstThreeMappedTotalHOne.map R G K) 1 := by
  let : IsIso ((bicomplexMap R G K).f 0) := row_isIso R G K 0 (by decide)
  let : IsIso ((bicomplexMap R G K).f 1) := row_isIso R G K 1 (by decide)
  let : IsIso ((bicomplexMap R G K).f 2) := row_isIso R G K 2 le_rfl
  exact Module.TotalOneQuasiIso.ModuleTotalHOneQuasiIso.quasiIsoAt (bicomplexMap R G K) inferInstance inferInstance inferInstance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotalOne.FirstThreeMappedTotalHOne
