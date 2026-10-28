import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution

/-! # Presentation Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationMap

noncomputable section

/-! The original free Čech presentation resolutions and their augmentations are functorial in the presentation presheaf. -/

open _root_.CategoryTheory Opposite

universe u v w

variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]
  {F G : Cᵒᵖ ⥤ Type u} (a : F ⟶ G)

def map : AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R F ⟶ AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.complex R G :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.down ℕ) (Functor.whiskerRight a (AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechExtra.NonemptyCechNerve.complexFunctor R))

theorem map_generator (n : ℕ) (U : Cᵒᵖ) (x : Fin (n + 1) → F.obj U) :
    ((PresentationMap.map R a).f n).app U (ModuleCat.freeMk x) = ModuleCat.freeMk (fun i => a.app U (x i)) :=
  ModuleCat.free_map_apply (R := R) (↾fun x : Fin (n + 1) → F.obj U => fun i => a.app U (x i)) x

theorem augmentation_generator (U : Cᵒᵖ) (x : Fin 1 → F.obj U) :
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R F).f 0).app U (ModuleCat.freeMk x) = (1 : R) := by
  change (ModuleCat.FreeMonoidal.εIso R).inv
    ((ModuleCat.free R).map (↾fun _ : Fin 1 → F.obj U => PUnit.unit) (ModuleCat.freeMk x)) = 1
  rw [ModuleCat.free_map_apply, ModuleCat.FreeMonoidal.εIso_inv_freeMk]

theorem augmentation : PresentationMap.map R a ≫ AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R G =
    AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R F := by
  apply HomologicalComplex.to_single_hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.free_hom_ext
  intro x
  change Fin 1 → F.obj U at x
  change ((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R G).f 0).app U (((PresentationMap.map R a).f 0).app U (ModuleCat.freeMk x)) = _
  exact (congrArg (((AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R G).f 0).app U) (map_generator R a 0 U x)).trans
    ((augmentation_generator R U (fun i => a.app U (x i))).trans (augmentation_generator R U x).symm)

instance map_isIso [IsIso a] : IsIso (PresentationMap.map R a) := by
  change IsIso ((AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.down ℕ)).map (Functor.whiskerRight a (AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechExtra.NonemptyCechNerve.complexFunctor R)))
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationMap
