import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionCoordinates

/-! # Restriction Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.RestrictionCoordinates

noncomputable section

/-! Restricting presentation cochains gives the actual restriction of sections on the frame tuple products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  [HasBinaryProducts C] [HasBinaryProducts D] (G : C ⥤ D) {ι : Type v}
  (F : ι → C) (H : ι → D) (a : ∀ i, G.obj (F i) ⟶ H i)
  (n : ℕ) (t : Fin (n + 1) → ι)
  (b : G.obj (TupleProducts.family F n t) ⟶ TupleProducts.family H n t)
  (hb : ∀ j, b ≫ Pi.π (fun j => H (t j)) j = G.map (Pi.π (fun j => F (t j)) j) ≫ a (t j))

include hb in
theorem universal : (fun j => (FamilyMap.Family.map G F H a).app
    (op (TupleProducts.family F n t)) (ResolutionCoordinates.universalTuple F n t j)) =
      (fun j => (CoveringPresentationPresheaf.presentations H).map b.op
        (ResolutionCoordinates.universalTuple H n t j)) := by
  funext j
  apply ULift.ext
  refine Sigma.ext (by rfl) ?_
  exact heq_of_eq (hb j).symm

variable (R : Type (max u v)) [CommRing R] (M : Dᵒᵖ ⥤ ModuleCat.{max u v} R)
  (f : (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R (CoveringPresentationPresheaf.presentations H)).X n ⟶ M)

include hb in
theorem presheaf : ResolutionCoordinates.presheaf F R n (G.op ⋙ M)
    ((Cech.PresentationRestriction.map R G (FamilyMap.Family.map G F H a)).f n ≫
      Functor.whiskerLeft G.op f) t =
        M.map b.op (ResolutionCoordinates.presheaf H R n M f t) := by
  let U := op (TupleProducts.family F n t)
  let x := ResolutionCoordinates.universalTuple F n t
  let y := ResolutionCoordinates.universalTuple H n t
  have ha := Cech.PresentationMap.map_generator R (FamilyMap.Family.map G F H a) n U x
  have hy : ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R (CoveringPresentationPresheaf.presentations H)).X n).map b.op
      (ModuleCat.freeMk y) = ModuleCat.freeMk (fun j => (CoveringPresentationPresheaf.presentations H).map b.op (y j)) :=
    ModuleCat.free_map_apply (R := R)
      (↾fun z : Fin (n + 1) → (CoveringPresentationPresheaf.presentations H).obj
        (op (TupleProducts.family H n t)) =>
          fun j => (CoveringPresentationPresheaf.presentations H).map b.op (z j)) y
  have hu := congrArg (ModuleCat.freeMk (R := R)) (universal G F H a n t b hb)
  have hf := congrArg (fun c => c (ModuleCat.freeMk y)) (f.naturality b.op)
  refine (ResolutionCoordinates.presheaf_apply F R n (G.op ⋙ M) _ t).trans ?_
  exact (congrArg (f.app (G.op.obj U)) (ha.trans (hu.trans hy.symm))).trans
    (hf.trans (congrArg (M.map b.op) (ResolutionCoordinates.presheaf_apply H R n M f t).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.RestrictionCoordinates
