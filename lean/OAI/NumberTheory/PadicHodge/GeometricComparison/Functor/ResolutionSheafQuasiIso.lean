import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafTotalEdge

/-! # Resolution Sheaf Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionSheafQuasiIso.FunctorResolutionSheafQuasiIso

noncomputable section

/-! A natural resolution functor computes every module-sheaf complex through its actual total augmentation. -/

open _root_.CategoryTheory

variable (R : Type) [CommRing R] (X : TopCat.{0})
  (G : TopCat.Sheaf (ModuleCat R) X ⥤ CochainComplex (TopCat.Sheaf (ModuleCat R) X) ℕ)
  [G.Additive] (η : CochainComplex.single₀ (TopCat.Sheaf (ModuleCat R) X) ⟶ G)

theorem quasiIso (hη : ∀ A, QuasiIso (η.app A))
    (K : CochainComplex (TopCat.Sheaf (ModuleCat R) X) ℕ) :
    QuasiIso (ResolutionTotal.FunctorResolutionTotal.edge G η K) :=
  Module.SheafTotalEdge.ModuleSheafTotalEdge.quasiIso R X (ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex G K) K
    (ResolutionBicomplex.FunctorResolutionBicomplex.augmentation G η K)
    (fun q q' _ => ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_comm G η K q q')
    (ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_comp_d G η K)
    (fun q => (ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_exact_mono G η K hη q).1)
    (fun q => (ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_exact_mono G η K hη q).2)
    (ResolutionBicomplex.FunctorResolutionBicomplex.row_exact G η K hη)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionSheafQuasiIso.FunctorResolutionSheafQuasiIso
