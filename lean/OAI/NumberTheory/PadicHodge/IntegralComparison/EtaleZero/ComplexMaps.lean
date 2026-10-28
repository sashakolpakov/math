import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.DeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.DeRhamMaps

/-! # Complex Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ComplexMaps

noncomputable section

/-!
# IntegralComparison: the actual lifted frame comparison is natural for chart algebra maps
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k C D : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [CommRing D] [Algebra k C] [Algebra k D] (f : C →ₐ[k] D)

def frameMap : BoundedEtale.ZeroFrameDeRhamIso.frameComplex p k C ⟶
    BoundedEtale.ZeroFrameDeRhamIso.frameComplex p k D :=
  ((DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (ZeroLevel.DeRhamMaps.pdMap p k C D f)

def deRhamMap : DeRham.Comparison.deRhamComplex p k C ⟶
    DeRham.Comparison.deRhamComplex p k D :=
  ((DeRham.Comparison.coefficientFunctor p k).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (ZeroLevel.DeRhamMaps.residueMap p k C D f)

theorem naturality : frameMap p k C D f ≫ (DeRham.Comparison.frameIso p k D).hom =
    (DeRham.Comparison.frameIso p k C).hom ≫ deRhamMap p k C D f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact congrArg (fun x => ULift.up (ULift.up x)) (ZeroLevel.DeRhamMaps.forms p k C D f n ω.down.down)

theorem homology_naturality (i : ℕ) :
    (HomologicalComplex.homologyFunctor _ _ i).map (frameMap p k C D f) ≫
      (HomologicalComplex.homologyFunctor _ _ i).map (DeRham.Comparison.frameIso p k D).hom =
    (HomologicalComplex.homologyFunctor _ _ i).map (DeRham.Comparison.frameIso p k C).hom ≫
      (HomologicalComplex.homologyFunctor _ _ i).map (deRhamMap p k C D f) := by
  rw [← Functor.map_comp, naturality, Functor.map_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ComplexMaps
