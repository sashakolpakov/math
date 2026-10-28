import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PresheafUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Refinement

/-! # Unit Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.UnitRefinement.IntrinsicCechPresheafUnit

noncomputable section

/-! The actual Čech sheafification unit is compatible with an actual cover refinement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  {ι κ : Type u} (U : ι → X.Opens) (V : κ → X.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ U (r i))
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

theorem refinement_naturality : Cech.Refinement.CechRefinement.map R X U V r hr F.obj ≫ (PresheafUnit.IntrinsicCechPresheafUnit.iso R X V F).hom =
    (PresheafUnit.IntrinsicCechPresheafUnit.iso R X U F).hom ≫
      ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).map
        ((Refinement.CechRefinement.sheafTransformation R X U V r hr).app F) :=
  (SheafificationComplex.SheafificationComplexUnit.naturality (Opens.grothendieckTopology X)
    (Cech.Refinement.CechRefinement.map R X U V r hr F.obj)).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.UnitRefinement.IntrinsicCechPresheafUnit
