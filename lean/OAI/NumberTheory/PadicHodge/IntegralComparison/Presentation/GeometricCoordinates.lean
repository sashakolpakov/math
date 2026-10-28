import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.GeometricRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.TupleRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.SheafRestrictionCoordinates

/-! # Geometric Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.GeometricCoordinates

noncomputable section

/-! The actual geometric presentation-resolution map is literal pullback
on the native tuple-section coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  [HasBinaryProducts C] [HasBinaryProducts D]
  (T : C ⥤ D) {ι κ : Type v} (F : ι → C) (G : κ → D) (ρ : ι → κ)
  (α : ∀ i, T.obj (F i) ⟶ G (ρ i)) (n : ℕ) (t : Fin (n + 1) → ι)

local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.TupleRefinement.map T F G ρ α n t
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.GeometricRefinement.presentationMap T F G ρ α

theorem universal :
    (fun j => (a).app (op (TupleProducts.family F n t))
      (ResolutionCoordinates.universalTuple F n t j)) =
        (fun j => (CoveringPresentationPresheaf.presentations G).map (b).op
          (ResolutionCoordinates.universalTuple G n (ρ ∘ t) j)) := by
  funext j
  apply ULift.ext
  refine Sigma.ext rfl ?_
  exact heq_of_eq (Frame.TupleRefinement.projection T F G ρ α n t j).symm

variable (R : Type (max u v)) [CommRing R] (M : Dᵒᵖ ⥤ ModuleCat.{max u v} R)

theorem presheaf
    (f : (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R (CoveringPresentationPresheaf.presentations G)).X n ⟶ M) :
    ResolutionCoordinates.presheaf F R n (T.op ⋙ M)
      ((Cech.PresentationRestriction.map R T a).f n ≫ Functor.whiskerLeft T.op f) t =
        M.map (b).op (ResolutionCoordinates.presheaf G R n M f (ρ ∘ t)) := by
  let U := op (TupleProducts.family F n t)
  let x := ResolutionCoordinates.universalTuple F n t
  let y := ResolutionCoordinates.universalTuple G n (ρ ∘ t)
  have ha := Cech.PresentationMap.map_generator R a n U x
  have hy : ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R (CoveringPresentationPresheaf.presentations G)).X n).map (b).op
      (ModuleCat.freeMk y) = ModuleCat.freeMk
        (fun j => (CoveringPresentationPresheaf.presentations G).map (b).op (y j)) :=
    ModuleCat.free_map_apply (R := R)
      (↾fun z : Fin (n + 1) → (CoveringPresentationPresheaf.presentations G).obj
        (op (TupleProducts.family G n (ρ ∘ t))) =>
          fun j => (CoveringPresentationPresheaf.presentations G).map (b).op (z j)) y
  have hu := congrArg (ModuleCat.freeMk (R := R)) (universal T F G ρ α n t)
  have hf := congrArg (fun c => c (ModuleCat.freeMk y)) (f.naturality (b).op)
  refine (ResolutionCoordinates.presheaf_apply F R n (T.op ⋙ M) _ t).trans ?_
  exact (congrArg (f.app (T.op.obj U)) (ha.trans (hu.trans hy.symm))).trans
    (hf.trans (congrArg (M.map (b).op)
      (ResolutionCoordinates.presheaf_apply G R n M f (ρ ∘ t)).symm))

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [T.IsContinuous J K] [T.IsCocontinuous J K]
  [∀ (M : Cᵒᵖ ⥤ ModuleCat.{max u v} R), T.op.HasPointwiseRightKanExtension M]
  (H : Sheaf K (ModuleCat.{max u v} R))

theorem sheaf (f : (CoveringPresentationResolution.complex K R G).X n ⟶ H) :
    ResolutionCoordinates.sheaf F R n J
      ((Cech.PresentationSheafRestriction.restriction R T J K).obj H)
      ((GeometricRefinement.map T F G ρ α R J K).f n ≫
        (Cech.PresentationSheafRestriction.restriction R T J K).map f) t =
          H.obj.map (b).op (ResolutionCoordinates.sheaf G R n K H f (ρ ∘ t)) := by
  have hu := SheafificationRestrictionHom.hom R T J K
    ((Cech.PresentationRestriction.map R T a).f n) f
  exact (congrArg (fun c => ResolutionCoordinates.presheaf F R n (T.op ⋙ H.obj) c t) hu).trans
    (presheaf T F G ρ α n t R H.obj
      (ResolutionCoordinates.unadjoint G R n K H f))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.GeometricCoordinates
