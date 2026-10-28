import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionToInjective

/-! # Exact Resolution Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExactResolutionTransport

noncomputable section

/-! An exact functor transports an augmented injective resolution to a
resolution, which maps into any target injective resolution. Preservation
of injective objects is not required. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {Y : C} {Y' : D} (s : F.obj Y ≅ Y')
  (I : InjectiveResolution Y) (I' : InjectiveResolution Y')

def complex : CochainComplex D ℕ := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex

def augmentation : (CochainComplex.single₀ D).obj Y' ⟶ complex F I :=
  Single.ComplexTransport.map F s I.ι

instance augmentation_quasiIso : QuasiIso (augmentation F s I) := by
  let : QuasiIso I.ι := I.quasiIso
  let : F.PreservesHomology := inferInstance
  have h₁ : QuasiIso ((Single.ComplexTransport.sourceIso F s).inv) := inferInstance
  have h₂ : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map I.ι) := inferInstance
  exact quasiIso_comp (Single.ComplexTransport.sourceIso F s).inv
    ((F.mapHomologicalComplex (.up ℕ)).map I.ι) (hφ := h₁) (hφ' := h₂)

def map : complex F I ⟶ I'.cocomplex :=
  Augmented.ResolutionToInjective.map (complex F I) (augmentation F s I) I' (𝟙 _)

theorem map_augmentation : augmentation F s I ≫ ExactResolutionTransport.map F s I I' = I'.ι :=
  (Augmented.ResolutionToInjective.augmentation (complex F I) (augmentation F s I) I' (𝟙 _)).trans
    ((congrArg (fun a => a ≫ I'.ι) ((CochainComplex.single₀ D).map_id _)).trans (Category.id_comp _))

omit [Abelian D] in
private theorem iso_square {A B V W : D} (e : A ≅ B)
    (a : A ⟶ V) (b : V ⟶ W) (d : B ⟶ W)
    (h : (e.inv ≫ a) ≫ b = d) : a ≫ b = e.hom ≫ d := by
  rw [← h, ← Category.assoc, ← Category.assoc, e.hom_inv_id, Category.id_comp]

theorem augmentation_square : F.map (I.ι.f 0) ≫ (ExactResolutionTransport.map F s I I').f 0 = s.hom ≫ I'.ι.f 0 :=
  iso_square s _ _ _
    ((congrArg (fun a => a ≫ (ExactResolutionTransport.map F s I I').f 0)
      (Single.ComplexTransport.map_zero F s I.ι).symm).trans
        (congrArg (fun a => a.f 0) (map_augmentation F s I I')))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExactResolutionTransport
