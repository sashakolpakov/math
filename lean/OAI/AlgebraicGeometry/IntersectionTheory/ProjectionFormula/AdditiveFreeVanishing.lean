import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Projectives
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Additive Free Vanishing -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdditiveFreeVanishing

noncomputable section

/-! An additive functor vanishing on the rank-one free module vanishes
on every finite free module, by its actual finite basis decomposition. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

variable (R : Type u) [CommRing R]
  {C : Type v} [Category.{w} C] [Preadditive C]
  (F : ModuleCat.{u} R ⥤ C) [F.Additive]

theorem isZero (hR : IsZero (F.obj (.of R R)))
    (P : ModuleCat.{u} R) [Module.Free R P] [Module.Finite R P] : IsZero (F.obj P) := by
  classical
  let b := Module.Free.chooseBasis R P
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex R P)
  let π (i : Module.Free.ChooseBasisIndex R P) : P ⟶ .of R R := ModuleCat.ofHom (b.coord i)
  let ι (i : Module.Free.ChooseBasisIndex R P) : ModuleCat.of R R ⟶ P :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R P (b i))
  have he : (𝟙 P) = ∑ i, π i ≫ ι i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
    change x = ∑ i, b.repr x i • b i
    exact (b.sum_repr x).symm
  apply (IsZero.iff_id_eq_zero (F.obj P)).mpr
  rw [← F.map_id, he, Functor.map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [F.map_comp, hR.eq_zero_of_src (F.map (ι i)), comp_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdditiveFreeVanishing
