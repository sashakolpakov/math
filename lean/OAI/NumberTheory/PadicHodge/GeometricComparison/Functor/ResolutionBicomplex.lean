import OAI.AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge

/-! # Resolution Bicomplex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex.FunctorResolutionBicomplex

noncomputable section

/-! A natural augmented resolution functor produces exact augmented bicomplex rows. -/

open _root_.CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (G : C ⥤ CochainComplex C ℕ) [G.Additive]
  (η : CochainComplex.single₀ C ⟶ G) (K : CochainComplex C ℕ)

def bicomplex : HomologicalComplex₂ C (.up ℕ) (.up ℕ) :=
  (G.mapHomologicalComplex (.up ℕ)).obj K

def augmentation (q : ℕ) : K.X q ⟶ ((bicomplex G K).X q).X 0 := (η.app (K.X q)).f 0

theorem augmentation_comm (q q' : ℕ) :
    augmentation G η K q ≫ ((bicomplex G K).d q q').f 0 =
      K.d q q' ≫ augmentation G η K q' := by
  have h := congrArg (fun f => f.f 0) (η.naturality (K.d q q'))
  exact h.symm.trans (congrArg (fun a => a ≫ (η.app (K.X q')).f 0)
    (CochainComplex.single₀_map_f_zero (K.d q q')))

theorem augmentation_comp_d (q : ℕ) :
    augmentation G η K q ≫ ((bicomplex G K).X q).d 0 1 = 0 := by
  have h := (η.app (K.X q)).comm 0 1
  exact h.trans ((congrArg (fun a => a ≫ (η.app (K.X q)).f 1)
    (HomologicalComplex.single_obj_d (.up ℕ) 0 (K.X q) 0 1)).trans zero_comp)

theorem augmentation_exact_mono (hη : ∀ A, QuasiIso (η.app A)) (q : ℕ) :
    (ShortComplex.mk (augmentation G η K q) (((bicomplex G K).X q).d 0 1)
      (augmentation_comp_d G η K q)).Exact ∧ Mono (augmentation G η K q) :=
  (AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation.CochainAugmentationCriterion.quasiIsoAt_zero_iff (η.app (K.X q))
    (HomologicalComplex.single_obj_d (.up ℕ) 0 (K.X q) 0 1)).mp ((hη (K.X q)).quasiIsoAt 0)

theorem row_exact (hη : ∀ A, QuasiIso (η.app A)) (q p : ℕ) :
    ((bicomplex G K).X q).ExactAt (p + 1) := by
  have : QuasiIso (η.app (K.X q)) := hη (K.X q)
  apply (exactAt_iff_of_quasiIsoAt (η.app (K.X q)) (p + 1)).mp
  exact HomologicalComplex.ExactAt.of_isZero
    (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 (K.X q) (p + 1) (by omega))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex.FunctorResolutionBicomplex
