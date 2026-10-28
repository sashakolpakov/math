import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechTerms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveAugmentationQuasi

/-! # Cech Injective Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechInjectiveResolution.LargeZariskiCechInjectiveResolution

noncomputable section

/-! # Additive images of the actual finite Čech resolution of an injective sheaf -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
  {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)) [Injective F]

def resolution : InjectiveResolution F where
  cocomplex := (MixedCech.Functor.MixedCechFunctor.sheafFunctor R X U).obj F
  injective := CechTerms.LargeZariskiCechTerms.term_injective R X F U
  ι := (MixedCech.Functor.MixedCechFunctor.sheafAugmentation R X U).app F
  quasiIso := MixedCech.Functor.MixedCechFunctor.sheafAugmentation_quasiIso R X U hU F

include hU in
theorem map_quasiIso {D : Type*} [Category D] [Abelian D]
    (G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R) ⥤ D) [G.Additive] :
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((MixedCech.Functor.MixedCechFunctor.sheafAugmentation R X U).app F)) :=
  InjectiveAugmentationQuasi.InjectiveAugmentation.map_quasiIso (resolution R X U hU F) G

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechInjectiveResolution.LargeZariskiCechInjectiveResolution
