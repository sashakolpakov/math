import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.FunctorCoordinates

/-! # Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Presheaf.Comparison

noncomputable section

/-! Actual original Ext resolution cochains are identified with any canonically isomorphic coefficient presheaf Čech complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v z

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  (H : Sheaf J (ModuleCat.{max u v} R)) (P : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (e : P ≅ H.obj)

local instance moduleProducts : HasProducts.{v} (ModuleCat.{max u v} R) := by
  let h : HasLimitsOfSize.{v, v} (ModuleCat.{max u v} R) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v, max u v}
  exact fun I => h.has_limits_of_shape (Discrete I)

def complex : CochainComplex (ModuleCat.{max u v z} R) ℕ :=
  ((ModuleCat.uliftFunctor.{z, max u v} R).mapHomologicalComplex (.up ℕ)).obj
    (Differential.complex F R P)

def comparison : Acyclic.ChainCohomology.complex R H
    (CoveringPresentationResolution.complex J R F) ≅ complex F R P :=
  FrameCech.Ext.Comparison.comparison F R J H ≪≫
    ((ModuleCat.uliftFunctor.{z, max u v} R).mapHomologicalComplex (.up ℕ)).mapIso
      ((NonemptyCechNerve.complexFunctor F).mapIso e.symm)

theorem coordinate_mk (n : ℕ) (t : Fin (n + 1) → ι)
    (f : (CoveringPresentationResolution.complex J R F).X n ⟶ H) :
    Differential.coordinate F R P n t
      (((comparison F R J H P e).hom.f n (Abelian.Ext.mk₀ f)).down) =
        e.inv.app (op (Presentation.TupleProducts.family F n t))
          (Presentation.ResolutionCoordinates.sheaf F R n J H f t) := by
  have h := congrArg (fun a => a (((FrameCech.Ext.Comparison.comparison F R J H).hom.f n (Abelian.Ext.mk₀ f)).down))
    (FunctorCoordinates.coordinate F R e.inv n t)
  exact h.trans (congrArg (e.inv.app (op (Presentation.TupleProducts.family F n t)))
    (ExtCoordinates.coordinate_mk F R J H n t f))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Presheaf.Comparison
