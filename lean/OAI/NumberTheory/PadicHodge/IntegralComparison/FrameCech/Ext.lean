import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SectionIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroContravariantSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCohomology

/-! # Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Ext.Comparison

noncomputable section

/-! Original Ext resolution cochains identify canonically with the actual frame Čech complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {ι : Type v} (F : ι → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  (H : Sheaf J (ModuleCat.{max u v} R))

def liftedComplex : CochainComplex (ModuleCat.{max u v z} R) ℕ :=
  ((ModuleCat.uliftFunctor.{z, max u v} R).mapHomologicalComplex (.up ℕ)).obj
    (Differential.complex F R H.obj)

def comparison : Acyclic.ChainCohomology.complex R H
    (CoveringPresentationResolution.complex J R F) ≅ liftedComplex F R J H :=
  (NatIso.mapHomologicalComplex (Ext.ZeroContravariantSections.iso R H) (.up ℕ)).app
    (CoveringPresentationResolution.complex J R F).op ≪≫
      ((ModuleCat.uliftFunctor.{z, max u v} R).mapHomologicalComplex (.up ℕ)).mapIso
        (SectionIso.iso F R J H)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.Ext.Comparison
