import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionCoordinates

/-! # Resolution Face Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionFaceMaps

noncomputable section

/-! Actual tuple face maps become the actual restrictions between frame products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) {n m : ℕ} (θ : Fin (m + 1) → Fin (n + 1))

def tupleMap : TupleProducts.tuples F n ⟶ TupleProducts.tuples F m where
  app _ := ↾fun x => x ∘ θ
  naturality _ _ _ := rfl

def productMap (t : Fin (n + 1) → ι) : TupleProducts.family F n t ⟶
    TupleProducts.family F m (t ∘ θ) :=
  Pi.lift (fun b => Pi.π (fun a => F (t a)) (θ b))

theorem universal_natural (t : Fin (n + 1) → ι) :
    (TupleProducts.tuples F m).map (productMap F θ t).op
      (ResolutionCoordinates.universalTuple F m (t ∘ θ)) =
        ResolutionCoordinates.universalTuple F n t ∘ θ := by
  funext b
  apply ULift.ext
  exact Sigma.ext rfl (heq_of_eq (Pi.lift_comp_π (fun a => Pi.π (fun j => F (t j)) (θ a)) b))

variable (R : Type (max u v)) [CommRing R]

def presheafMap :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R
      (CoveringPresentationPresheaf.presentations F)).X n ⟶
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R
      (CoveringPresentationPresheaf.presentations F)).X m :=
  Functor.whiskerRight (tupleMap F θ) (ModuleCat.free R)

omit [HasBinaryProducts C] in
theorem map_generator (U : Cᵒᵖ)
    (x : Fin (n + 1) → (CoveringPresentationPresheaf.presentations F).obj U) :
    (presheafMap F θ R).app U (ModuleCat.freeMk x) = ModuleCat.freeMk (x ∘ θ) :=
  ModuleCat.free_map_apply (R := R) ((tupleMap F θ).app U) x

theorem restriction_generator (t : Fin (n + 1) → ι) :
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R
      (CoveringPresentationPresheaf.presentations F)).X m).map (productMap F θ t).op
      (ModuleCat.freeMk (ResolutionCoordinates.universalTuple F m (t ∘ θ))) =
        ModuleCat.freeMk (ResolutionCoordinates.universalTuple F n t ∘ θ) :=
  (ModuleCat.free_map_apply (R := R) ((TupleProducts.tuples F m).map (productMap F θ t).op)
    (ResolutionCoordinates.universalTuple F m (t ∘ θ))).trans
      (congrArg ModuleCat.freeMk (universal_natural F θ t))

theorem presheaf_coordinates (H : Cᵒᵖ ⥤ ModuleCat.{max u v} R)
    (a : (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R
      (CoveringPresentationPresheaf.presentations F)).X m ⟶ H) (t : Fin (n + 1) → ι) :
    ResolutionCoordinates.presheaf F R n H (presheafMap F θ R ≫ a) t =
      H.map (productMap F θ t).op (ResolutionCoordinates.presheaf F R m H a (t ∘ θ)) := by
  have h := congrArg (fun b => b (ModuleCat.freeMk
    (ResolutionCoordinates.universalTuple F m (t ∘ θ))))
      (a.naturality (productMap F θ t).op)
  have hl := congrArg (a.app (op (TupleProducts.family F n t)))
    (map_generator F θ R (op (TupleProducts.family F n t))
      (ResolutionCoordinates.universalTuple F n t))
  have hr := congrArg (a.app (op (TupleProducts.family F n t)))
    (restriction_generator F θ R t)
  exact (ResolutionCoordinates.presheaf_apply F R n H (presheafMap F θ R ≫ a) t).trans
    (hl.trans (hr.symm.trans (h.trans
      (congrArg (H.map (productMap F θ t).op)
        (ResolutionCoordinates.presheaf_apply F R m H a (t ∘ θ)).symm))))

def sheafMap (J : GrothendieckTopology C) :
    (CoveringPresentationResolution.complex J R F).X n ⟶
      (CoveringPresentationResolution.complex J R F).X m :=
  (presheafToSheaf J (ModuleCat.{max u v} R)).map (presheafMap F θ R)

theorem sheaf_coordinates (J : GrothendieckTopology C) (H : Sheaf J (ModuleCat.{max u v} R))
    (a : (CoveringPresentationResolution.complex J R F).X m ⟶ H) (t : Fin (n + 1) → ι) :
    ResolutionCoordinates.sheaf F R n J H (sheafMap F θ R J ≫ a) t =
      H.obj.map (productMap F θ t).op (ResolutionCoordinates.sheaf F R m J H a (t ∘ θ)) := by
  have h := (sheafificationAdjunction J (ModuleCat.{max u v} R)).homEquiv_naturality_left
    (presheafMap F θ R) a
  exact (congrArg (fun b => ResolutionCoordinates.presheaf F R n H.obj b t) h).trans
    (presheaf_coordinates F θ R H.obj (ResolutionCoordinates.unadjoint F R m J H a) t)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionFaceMaps
