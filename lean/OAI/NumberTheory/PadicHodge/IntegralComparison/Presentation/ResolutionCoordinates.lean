import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationLinearSections

/-! # Resolution Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionCoordinates

noncomputable section

/-! Coefficient-linear coordinates for the actual frame presentation chain terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R] (n : ℕ)

def presheaf (H : Cᵒᵖ ⥤ ModuleCat.{max u v} R) :
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R
      (CoveringPresentationPresheaf.presentations F)).X n ⟶ H) ≃ₗ[R]
        (∀ t, H.obj (op (TupleProducts.family F n t))) :=
  (Linear.homCongr R (ResolutionTerms.presheafIso F R n) (Iso.refl H)).trans
    (Free.PresentationLinearSections.presheaf (TupleProducts.family F n) R H)

def unadjoint (J : GrothendieckTopology C) (H : Sheaf J (ModuleCat.{max u v} R))
    (a : (CoveringPresentationResolution.complex J R F).X n ⟶ H) :
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R
      (CoveringPresentationPresheaf.presentations F)).X n ⟶ H.obj :=
  (sheafificationAdjunction J (ModuleCat.{max u v} R)).homEquiv _ H a

def sheaf (J : GrothendieckTopology C) (H : Sheaf J (ModuleCat.{max u v} R)) :
    ((CoveringPresentationResolution.complex J R F).X n ⟶ H) ≃ₗ[R]
      (∀ t, H.obj.obj (op (TupleProducts.family F n t))) :=
  (LinearAdjunction.homLinearEquiv R (sheafificationAdjunction J (ModuleCat.{max u v} R))
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R
      (CoveringPresentationPresheaf.presentations F)).X n) H).trans (presheaf F R n H.obj)

def universalTuple (t : Fin (n + 1) → ι) :
    Fin (n + 1) → (CoveringPresentationPresheaf.presentations F).obj
      (op (TupleProducts.family F n t)) :=
  fun a => ⟨⟨t a, Pi.π (fun b => F (t b)) a⟩⟩

theorem presheaf_apply (H : Cᵒᵖ ⥤ ModuleCat.{max u v} R)
    (a : (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R
      (CoveringPresentationPresheaf.presentations F)).X n ⟶ H) (t : Fin (n + 1) → ι) :
    presheaf F R n H a t = a.app (op (TupleProducts.family F n t))
      (ModuleCat.freeMk (universalTuple F n t)) := by
  change a.app (op (TupleProducts.family F n t))
    ((ModuleCat.free R).map (TupleProducts.equiv F n
      (TupleProducts.family F n t)).symm.toIso.hom
        (ModuleCat.freeMk ⟨⟨t, 𝟙 (TupleProducts.family F n t)⟩⟩)) = _
  have h := ModuleCat.free_map_apply (R := R)
    (TupleProducts.equiv F n (TupleProducts.family F n t)).symm.toIso.hom
    ⟨⟨t, 𝟙 (TupleProducts.family F n t)⟩⟩
  have he : (TupleProducts.equiv F n
      (TupleProducts.family F n t)).symm ⟨⟨t, 𝟙 _⟩⟩ = universalTuple F n t := by
    funext b
    apply ULift.ext
    exact Sigma.ext rfl (heq_of_eq (Category.id_comp _))
  exact congrArg (a.app (op (TupleProducts.family F n t)))
    (h.trans (congrArg ModuleCat.freeMk he))

theorem sheaf_apply (J : GrothendieckTopology C) (H : Sheaf J (ModuleCat.{max u v} R))
    (a : (CoveringPresentationResolution.complex J R F).X n ⟶ H) (t : Fin (n + 1) → ι) :
    sheaf F R n J H a t = (unadjoint F R n J H a).app (op (TupleProducts.family F n t))
      (ModuleCat.freeMk (universalTuple F n t)) :=
  presheaf_apply F R n H.obj (unadjoint F R n J H a) t

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionCoordinates
