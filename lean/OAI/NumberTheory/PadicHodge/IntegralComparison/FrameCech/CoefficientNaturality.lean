import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.FunctorCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ProductScalarKernel

/-! # Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.CoefficientNaturality

noncomputable section

/-! Coefficient maps in the original Ext resolution retain the canonical
native frame Čech section coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v z

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  {H H' : Sheaf J (ModuleCat.{max u v} R)} (μ : H ⟶ H')

local instance moduleProducts : HasProducts.{v} (ModuleCat.{max u v} R) := by
  let h : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v, max u v}
  exact fun I => h.has_limits_of_shape (Discrete I)

def map : FrameCech.Ext.Comparison.liftedComplex.{u, v, z} F R J H ⟶
    FrameCech.Ext.Comparison.liftedComplex.{u, v, z} F R J H' :=
  ((ModuleCat.uliftFunctor.{z, max u v} R).mapHomologicalComplex (.up ℕ)).map
    ((NonemptyCechNerve.complexFunctor F).map μ.hom)

def resolutionMap := Acyclic.ChainCoefficientNaturality.complexMap R μ
  (CoveringPresentationResolution.complex J R F)

omit [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))] in
theorem sections (n : ℕ) (f : (CoveringPresentationResolution.complex J R F).X n ⟶ H)
    (t : Fin (n + 1) → ι) :
    Presentation.ResolutionCoordinates.sheaf F R n J H' (f ≫ μ) t =
      μ.hom.app (op (Presentation.TupleProducts.family F n t))
        (Presentation.ResolutionCoordinates.sheaf F R n J H f t) := by
  let U := op (Presentation.TupleProducts.family F n t)
  let x := ModuleCat.freeMk (R := R) (Presentation.ResolutionCoordinates.universalTuple F n t)
  have hn := (sheafificationAdjunction J (ModuleCat.{max u v} R)).homEquiv_naturality_right f μ
  exact (Presentation.ResolutionCoordinates.sheaf_apply F R n J H' (f ≫ μ) t).trans
    ((congrArg (fun a => a.app U x) hn).trans
      (congrArg (μ.hom.app U) (Presentation.ResolutionCoordinates.sheaf_apply F R n J H f t).symm))

theorem complexes : resolutionMap F R J μ ≫ (FrameCech.Ext.Comparison.comparison F R J H').hom =
    (FrameCech.Ext.Comparison.comparison F R J H).hom ≫ CoefficientNaturality.map F R J μ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Abelian.Ext.{max u v z} ((CoveringPresentationResolution.complex J R F).X n) H 0 at x
  obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
  apply ULift.ext
  apply Module.ProductScalarKernel.element_ext
    (fun t => H'.obj.obj (op (Presentation.TupleProducts.family F n t)))
  intro t
  have hm : (resolutionMap F R J μ).f n (Abelian.Ext.mk₀ f) = Abelian.Ext.mk₀ (f ≫ μ) :=
    Abelian.Ext.mk₀_comp_mk₀ _ _
  have hl := (congrArg (fun x => Differential.coordinate F R H'.obj n t
    (((FrameCech.Ext.Comparison.comparison F R J H').hom.f n x).down)) hm).trans
      ((ExtCoordinates.coordinate_mk F R J H' n t (f ≫ μ)).trans (sections F R J μ n f t))
  have hr := (congrArg (fun a => a
    (((FrameCech.Ext.Comparison.comparison F R J H).hom.f n (Abelian.Ext.mk₀ f)).down))
      (FunctorCoordinates.coordinate F R μ.hom n t)).trans
        (congrArg (μ.hom.app (op (Presentation.TupleProducts.family F n t)))
          (ExtCoordinates.coordinate_mk F R J H n t f))
  exact hl.trans hr.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.CoefficientNaturality
