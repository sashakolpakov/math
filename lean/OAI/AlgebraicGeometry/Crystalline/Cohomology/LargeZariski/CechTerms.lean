import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.OpenPushforward
import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveProductsCore
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Cech Terms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechTerms.LargeZariskiCechTerms

noncomputable section

/-!
# Injectivity of finite Čech sheaf terms

Each intersection coefficient sheaf is the actual direct image of an
open restriction. On a finite cover, exact sheafification preserves
the finite product defining every Čech degree.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R))

local instance coefficientLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

def intersectionPresheafIso (W : X.Opens) :
    ((OpenPushforward.LargeZariskiOpenPushforward.intersection R W).obj F).obj ≅
      MixedCech.Presheaf.MixedCechPresheaf.intersection R X F.obj W :=
  NatIso.ofComponents
    (fun V => F.obj.mapIso (eqToIso (congrArg op (show
      W.ι ''ᵁ (W.ι ⁻¹ᵁ V.unop) = V.unop ⊓ W by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
          Scheme.Opens.opensRange_ι, inf_comm]))))
    (by
      intro V Z f
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1)

def intersectionIso (W : X.Opens) :
    (MixedCech.Presheaf.MixedCechPresheaf.sheafification R X).obj
      (MixedCech.Presheaf.MixedCechPresheaf.intersection R X F.obj W) ≅
        (OpenPushforward.LargeZariskiOpenPushforward.intersection R W).obj F :=
  ((MixedCech.Presheaf.MixedCechPresheaf.sheafification R X).mapIso
    (intersectionPresheafIso R X F W)).symm ≪≫
      (sheafificationIso ((OpenPushforward.LargeZariskiOpenPushforward.intersection R W).obj F)).symm

variable {ι : Type u} [Finite ι] (U : ι → X.Opens)

def termIso (n : ℕ) : ((MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U).obj F).X n ≅
    ∏ᶜ (fun t : Fin (n + 1) → ι =>
      (OpenPushforward.LargeZariskiOpenPushforward.intersection R (∏ᶜ (U ∘ t))).obj F) :=
  PreservesProduct.iso (MixedCech.Presheaf.MixedCechPresheaf.sheafification R X)
    (fun t : Fin (n + 1) → ι =>
      MixedCech.Presheaf.MixedCechPresheaf.intersection R X F.obj (∏ᶜ (U ∘ t))) ≪≫
        Pi.mapIso (fun t => intersectionIso R X F (∏ᶜ (U ∘ t)))

theorem term_injective [Injective F] (n : ℕ) :
    Injective (((MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U).obj F).X n) :=
  Injective.of_iso (termIso R X F U n).symm
    (InjectiveProductsCore.InjectiveProducts.injective (fun t : Fin (n + 1) → ι =>
      (OpenPushforward.LargeZariskiOpenPushforward.intersection R (∏ᶜ (U ∘ t))).obj F))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechTerms.LargeZariskiCechTerms
