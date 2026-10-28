import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Ideal Quotient Maps -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IdealQuotientMaps.IdealQuotientOpenMaps

noncomputable section

/-! Restriction between quotient rings on arbitrary affine opens is the
original open immersion between the corresponding closed-subscheme charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData) {U V : X.affineOpens} (h : U ≤ V)

theorem map_cover : I.glueDataObjMap h ≫ I.subschemeCover.f V = I.subschemeCover.f U := by
  apply (cancel_mono I.subschemeι).mp
  erw [Category.assoc, I.subschemeCover_map_subschemeι, ← Category.assoc,
    I.glueDataObjMap_glueDataObjι, Category.assoc, Scheme.homOfLE_ι,
    I.subschemeCover_map_subschemeι]

theorem openImmersion : IsOpenImmersion (I.glueDataObjMap h) := by
  have hcomp : IsOpenImmersion (I.glueDataObjMap h ≫ I.subschemeCover.f V) := by
    rw [map_cover]
    exact I.subschemeCover.map_prop U
  exact @IsOpenImmersion.of_comp _ _ _ (I.glueDataObjMap h) (I.subschemeCover.f V)
    (I.subschemeCover.map_prop V) hcomp

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IdealQuotientMaps.IdealQuotientOpenMaps
