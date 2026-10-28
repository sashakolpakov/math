import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.TupleRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionCoordinates

/-! # Family Refinement Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyRefinementCoordinates.Family

noncomputable section

/-! The map on the original free presentation resolution has exactly the
tuple-section coordinates of the native Čech refinement map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι κ : Type v} (F : ι → C) (G : κ → C) (ρ : ι → κ) (α : ∀ i, F i ⟶ G (ρ i))
  (n : ℕ) (t : Fin (n + 1) → ι)

local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.TupleRefinement.map (𝟭 C) F G ρ α n t
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyRefinement.Family.presentationMap F G ρ α

theorem universal :
    (fun j => (a).app (op (TupleProducts.family F n t))
      (ResolutionCoordinates.universalTuple F n t j)) =
        (fun j => (CoveringPresentationPresheaf.presentations G).map (b).op
          (ResolutionCoordinates.universalTuple G n (ρ ∘ t) j)) := by
  funext j
  apply ULift.ext
  refine Sigma.ext rfl ?_
  exact heq_of_eq (Frame.TupleRefinement.projection (𝟭 C) F G ρ α n t j).symm

variable (R : Type (max u v)) [CommRing R] (M : Cᵒᵖ ⥤ ModuleCat.{max u v} R)
  (f : (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R (CoveringPresentationPresheaf.presentations G)).X n ⟶ M)

theorem presheaf : ResolutionCoordinates.presheaf F R n M
    ((Cech.PresentationMap.map R a).f n ≫ f) t =
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
  have hu := congrArg (ModuleCat.freeMk (R := R)) (universal F G ρ α n t)
  have hf := congrArg (fun c => c (ModuleCat.freeMk y)) (f.naturality (b).op)
  refine (ResolutionCoordinates.presheaf_apply F R n M _ t).trans ?_
  exact (congrArg (f.app U) (ha.trans (hu.trans hy.symm))).trans
    (hf.trans (congrArg (M.map (b).op)
      (ResolutionCoordinates.presheaf_apply G R n M f (ρ ∘ t)).symm))

variable (J : GrothendieckTopology C) (H : Sheaf J (ModuleCat.{max u v} R))

theorem sheaf (f : (CoveringPresentationResolution.complex J R G).X n ⟶ H) :
    ResolutionCoordinates.sheaf F R n J H
      ((FamilyRefinement.Family.map F G ρ α R J).f n ≫ f) t =
        H.obj.map (b).op (ResolutionCoordinates.sheaf G R n J H f (ρ ∘ t)) := by
  have hu := (sheafificationAdjunction J (ModuleCat.{max u v} R)).homEquiv_naturality_left
    ((Cech.PresentationMap.map R a).f n) f
  exact (congrArg (fun c => ResolutionCoordinates.presheaf F R n H.obj c t) hu).trans
    (presheaf F G ρ α n t R H.obj
      (ResolutionCoordinates.unadjoint G R n J H f))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyRefinementCoordinates.Family
