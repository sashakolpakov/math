import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionExact

/-! # Reduction Sequence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionSequence.IntrinsicIntegralReductionSequence

noncomputable section

/-! The actual reduction morphism is part of a cochain short complex, exact in the first two degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionComplex.IntrinsicIntegralReductionComplex

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (r : R) (hr : algebraMap R S r = 0)

include hr

theorem presheaf_zero : (r • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)) ≫
    ReductionComplex.IntrinsicIntegralReductionComplex.presheafMap R S X Y f h = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact (ReductionExact.IntrinsicIntegralReductionExact.sequence R S X Y f h n r hr).zero

theorem sheaf_zero : (r • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) ≫
    ReductionComplex.IntrinsicIntegralReductionComplex.sheafMap R S X Y f h = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  have hh := congrArg
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).map
    (ReductionExact.IntrinsicIntegralReductionExact.sequence R S X Y f h n r hr).zero
  rw [Functor.map_comp, Functor.map_zero] at hh
  change (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).map
    (r • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)) ≫ _ = 0 at hh
  rw [Functor.map_smul, CategoryTheory.Functor.map_id] at hh
  exact hh

def sequence : ShortComplex (CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℕ) :=
  ShortComplex.mk (r • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) (ReductionComplex.IntrinsicIntegralReductionComplex.sheafMap R S X Y f h)
    (sheaf_zero R S X Y f h r hr)

def degreeIso (n : ℕ) :
    ((sequence R S X Y f h r hr).map
      (HomologicalComplex.eval (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) (.up ℕ) n)) ≅
    (ReductionExact.IntrinsicIntegralReductionExact.sequence R S X Y f h n r hr).map
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 _ ≫ (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).map
        (r • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)) = (r • 𝟙 _) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id, Functor.map_smul, CategoryTheory.Functor.map_id]
      rfl)
    (by
      change 𝟙 _ ≫ (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).map
        (ReductionPresheaf.IntrinsicIntegralReductionPresheaf.map R S X Y f h n) = _ ≫ 𝟙 _
      erw [Category.id_comp])

theorem low_shortExact [Smooth X.hom]
    (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hS : Function.Surjective (algebraMap R S))
    (hker : RingHom.ker (algebraMap R S) = Ideal.span {r}) (hreg : IsRegular r)
    (n : ℕ) (hn : n ≤ 1) :
    ((sequence R S X Y f h r hr).map
      (HomologicalComplex.eval (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) (.up ℕ) n)).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso (degreeIso R S X Y f h r hr n)).mpr
    (ReductionExact.IntrinsicIntegralReductionExact.shortExact R S X Y f h hp hS n hn r hr hker hreg)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionSequence.IntrinsicIntegralReductionSequence
