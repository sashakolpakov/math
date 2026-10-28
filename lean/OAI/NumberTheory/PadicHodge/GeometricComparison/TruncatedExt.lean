import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Category.Grp.Zero

/-! # Truncated Ext -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedExt.TruncatedExtVanishing

noncomputable section

/-! Positive coefficient Ext vanishing survives the actual Hodge truncations and extension to integer degrees. -/

open _root_.CategoryTheory Abelian Limits ZeroObject Opposite

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (A : C) (K : CochainComplex C ℕ)
  (hK : ∀ p q, Subsingleton (Ext.{w} A (K.X p) (q + 1)))

include hK in
theorem brutal (r : ℤ) (p q : ℕ) :
    Subsingleton (Ext.{w} A ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).X p) (q + 1)) := by
  let H := (extFunctor.{w} (q + 1) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}).obj (op A)
  have : H.Additive := inferInstanceAs ((extFunctorObj A (q + 1)).Additive)
  change Subsingleton (H.obj (if r ≤ (p : ℤ) then K.X p else 0))
  split_ifs with hp
  · exact hK p q
  · exact AddCommGrpCat.subsingleton_of_isZero (H.map_isZero (isZero_zero C))

include hK in
theorem extend (p : ℤ) (q : ℕ) :
    Subsingleton (Ext.{w} A ((K.extend ComplexShape.embeddingUpNat).X p) (q + 1)) := by
  let H := (extFunctor.{w} (q + 1) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}).obj (op A)
  have : H.Additive := inferInstanceAs ((extFunctorObj A (q + 1)).Additive)
  cases p with
  | ofNat n =>
    have : Subsingleton (H.obj (K.X n)) := hK n q
    let e := H.mapIso (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
    exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton
  | negSucc n =>
    exact AddCommGrpCat.subsingleton_of_isZero (H.map_isZero
      (CochainComplex.isZero_of_isStrictlyGE (K.extend ComplexShape.embeddingUpNat)
        0 (Int.negSucc n) (by omega)))

include hK in
theorem brutal_extend (r p : ℤ) (q : ℕ) :
    Subsingleton (Ext.{w} A (((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).extend
      ComplexShape.embeddingUpNat).X p) (q + 1)) :=
  TruncatedExtVanishing.extend A (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) (brutal A K hK r) p q

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedExt.TruncatedExtVanishing
