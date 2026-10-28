import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Bicomplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.CoefficientNaturality

/-! # Ext Bicomplex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtBicomplex

noncomputable section

/-! For the actual covering-presentation resolution, the mixed Hom
bicomplex is canonically the native frame Čech bicomplex of the coefficient
complex. The identification respects both differentials. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]

local instance moduleProducts : HasProducts.{v} (ModuleCat.{max u v} R) := by
  let h : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v, max u v}
  exact fun I => h.has_limits_of_shape (Discrete I)

def liftedFunctor : Sheaf J (ModuleCat.{max u v} R) ⥤
    CochainComplex (ModuleCat.{max u v z} R) ℕ :=
  sheafToPresheaf J (ModuleCat.{max u v} R) ⋙ NonemptyCechNerve.complexFunctor F ⋙
    (ModuleCat.uliftFunctor.{z, max u v} R).mapHomologicalComplex (.up ℕ)

def functorIso :
    ResolutionHom.Bicomplex.functor R (CoveringPresentationResolution.complex J R F) ≅
      liftedFunctor.{u, v, z} F R J :=
  NatIso.ofComponents (Ext.Comparison.comparison F R J)
    (fun μ => CoefficientNaturality.complexes F R J μ)

instance liftedFunctor_additive : (liftedFunctor.{u, v, z} F R J).Additive :=
  Functor.additive_of_iso (functorIso.{u, v, z} F R J)

variable (K : CochainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ)

def bicomplexIso :
    ResolutionHom.Bicomplex.bicomplex R (CoveringPresentationResolution.complex J R F) K ≅
      ((liftedFunctor.{u, v, z} F R J).mapHomologicalComplex (.up ℕ)).obj K :=
  (NatIso.mapHomologicalComplex (functorIso.{u, v, z} F R J) (.up ℕ)).app K

theorem bicomplexIso_component (b : ℕ) :
    (bicomplexIso.{u, v, z} F R J K).hom.f b =
      (Ext.Comparison.comparison.{u, v, z} F R J (K.X b)).hom := rfl

theorem naturality {L : CochainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ} (g : K ⟶ L) :
    ResolutionHom.Bicomplex.map R (CoveringPresentationResolution.complex J R F) g ≫
      (bicomplexIso.{u, v, z} F R J L).hom =
        (bicomplexIso.{u, v, z} F R J K).hom ≫
          ((liftedFunctor.{u, v, z} F R J).mapHomologicalComplex (.up ℕ)).map g :=
  (NatIso.mapHomologicalComplex (functorIso.{u, v, z} F R J) (.up ℕ)).hom.naturality g

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtBicomplex
