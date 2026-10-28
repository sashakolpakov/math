import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionTotal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.SheafTotalEdge

/-! # Resolution Sheaf Quasi Iso -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ResolutionSheafQuasiIso.FunctorResolutionSheafQuasiIso

noncomputable section

/-! A natural resolution functor computes every module-sheaf complex through its actual total augmentation. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R] (X : TopCat.{u})
  (G : TopCat.Sheaf (ModuleCat.{u} R) X ⥤ CochainComplex (TopCat.Sheaf (ModuleCat.{u} R) X) ℕ)
  [G.Additive] (η : CochainComplex.single₀ (TopCat.Sheaf (ModuleCat.{u} R) X) ⟶ G)

theorem quasiIso (hη : ∀ A, QuasiIso (η.app A))
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{u} R) X) ℕ) :
    QuasiIso (NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionTotal.FunctorResolutionTotal.edge G η K) :=
  Module.SheafTotalEdge.ModuleSheafTotalEdge.quasiIso R X (NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex G K) K
    (NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex.FunctorResolutionBicomplex.augmentation G η K)
    (fun q q' _ => NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_comm G η K q q')
    (NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_comp_d G η K)
    (fun q => (NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_exact_mono G η K hη q).1)
    (fun q => (NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_exact_mono G η K hη q).2)
    (NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex.FunctorResolutionBicomplex.row_exact G η K hη)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ResolutionSheafQuasiIso.FunctorResolutionSheafQuasiIso
