import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionFaceMaps

/-! # Resolution Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionDifferential

noncomputable section

/-! The original chain differential is the alternating sum of the actual tuple face maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicTopology

universe u v

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R]

omit [HasBinaryProducts C] in
theorem presheaf (n : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R
      (CoveringPresentationPresheaf.presentations F)).d (n + 1) n =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          ResolutionFaceMaps.presheafMap F i.succAbove R := by
  apply NatTrans.ext
  funext U
  simp only [NatTrans.app_sum, NatTrans.app_zsmul]
  exact AlternatingFaceMapComplex.obj_d_eq
    (AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechExtra.NonemptyCechNerve.nerve
      ((CoveringPresentationPresheaf.presentations F).obj U) ⋙ ModuleCat.free R) n

omit [HasBinaryProducts C] in
theorem sheaf (J : GrothendieckTopology C) (n : ℕ) :
    (CoveringPresentationResolution.complex J R F).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        ResolutionFaceMaps.sheafMap F i.succAbove R J := by
  change (presheafToSheaf J (ModuleCat.{max u v} R)).map
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R
      (CoveringPresentationPresheaf.presentations F)).d (n + 1) n) = _
  rw [presheaf, Functor.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (presheafToSheaf J (ModuleCat.{max u v} R)).map_zsmul

theorem coordinates (J : GrothendieckTopology C) (H : Sheaf J (ModuleCat.{max u v} R)) (n : ℕ)
    (a : (CoveringPresentationResolution.complex J R F).X n ⟶ H) (t : Fin (n + 2) → ι) :
    ResolutionCoordinates.sheaf F R (n + 1) J H
      ((CoveringPresentationResolution.complex J R F).d (n + 1) n ≫ a) t =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • H.obj.map
          (ResolutionFaceMaps.productMap F i.succAbove t).op
          (ResolutionCoordinates.sheaf F R n J H a (t ∘ i.succAbove)) := by
  rw [sheaf, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun x => (-1 : ℤ) ^ (i : ℕ) • x)
    (ResolutionFaceMaps.sheaf_coordinates F i.succAbove R J H a t)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionDifferential
