import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaSliceSections

/-! # Presentation Sheaf Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationSheafSections

noncomputable section

/-! The original free presentation sheaf has the same section families as its free representable summands. -/

open _root_.CategoryTheory Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] {ι : Type v} (F : ι → C)
  (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasSheafify J (ModuleCat.{max u v} R)]

abbrev sheaf : Sheaf J (ModuleCat.{max u v} R) :=
  (presheafToSheaf J (ModuleCat.{max u v} R)).obj (PresentationSections.presheaf F R)

def homEquiv (H : Sheaf J (ModuleCat.{max u v} R)) :
    (sheaf F R J ⟶ H) ≃+ (∀ i, H.obj.obj (op (F i))) :=
  ((sheafificationAdjunction J (ModuleCat.{max u v} R)).homAddEquiv
    (PresentationSections.presheaf F R) H).trans (PresentationSections.homEquiv F R H.obj)

theorem homEquiv_natural {H K : Sheaf J (ModuleCat.{max u v} R)} (g : H ⟶ K)
    (a : sheaf F R J ⟶ H) (i : ι) :
    homEquiv F R J K (a ≫ g) i = g.hom.app (op (F i)) (homEquiv F R J H a i) := by
  change (presheafToSheaf J (ModuleCat.{max u v} R)).obj
    (PresentationSections.presheaf F R) ⟶ H at a
  exact congrArg (fun b => PresentationSections.homEquiv F R K.obj b i)
    ((sheafificationAdjunction J (ModuleCat.{max u v} R)).homEquiv_naturality_right a g)

def freeSections (U : C) (H : Sheaf J (ModuleCat.{max u v} R)) :
    (Sheaf.freeYoneda J U (ModuleCat.of R R) ⟶ H) ≃+ H.obj.obj (op U) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaAddEquiv.FreeYonedaAddEquiv.sheaf J U (ModuleCat.of R R) H).trans
    (ModuleCat.homAddEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ (H.obj.obj (op U))).toAddEquiv)

theorem freeSections_natural (U : C) {H K : Sheaf J (ModuleCat.{max u v} R)} (g : H ⟶ K)
    (a : Sheaf.freeYoneda J U (ModuleCat.of R R) ⟶ H) :
    freeSections R J U K (a ≫ g) = g.hom.app (op U) (freeSections R J U H a) :=
  congrArg (fun b => b (1 : R)) (YonedaSliceSections.free_natural J U (ModuleCat.of R R) g a)

def familyEquiv (H : Sheaf J (ModuleCat.{max u v} R)) :
    (sheaf F R J ⟶ H) ≃+ (∀ i, Sheaf.freeYoneda J (F i) (ModuleCat.of R R) ⟶ H) :=
  (homEquiv F R J H).trans (AddEquiv.piCongrRight (fun i => freeSections R J (F i) H)).symm

theorem freeSections_family (H : Sheaf J (ModuleCat.{max u v} R))
    (a : sheaf F R J ⟶ H) (i : ι) :
    freeSections R J (F i) H (familyEquiv F R J H a i) = homEquiv F R J H a i :=
  (freeSections R J (F i) H).apply_symm_apply _

theorem familyEquiv_natural {H K : Sheaf J (ModuleCat.{max u v} R)} (g : H ⟶ K)
    (a : sheaf F R J ⟶ H) (i : ι) :
    familyEquiv F R J K (a ≫ g) i = familyEquiv F R J H a i ≫ g := by
  apply (freeSections R J (F i) K).injective
  exact (freeSections_family F R J K (a ≫ g) i).trans
    ((homEquiv_natural F R J g a i).trans
      ((congrArg (g.hom.app (op (F i))) (freeSections_family F R J H a i).symm).trans
        (freeSections_natural R J (F i) g (familyEquiv F R J H a i)).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationSheafSections
