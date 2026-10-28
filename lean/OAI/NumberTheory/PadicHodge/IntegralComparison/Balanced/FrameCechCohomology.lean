import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoefficientEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Frame Cech Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameCechCohomology

noncomputable section

/-! The balanced original Ext comparison is normalized by the actual
coefficient augmentation into the native frame Čech bicomplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z w

variable {C : Type (max u v)} [Category.{v} C] [HasBinaryProducts C]
  {κ : Type v} (F : κ → C) (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u v z} (Sheaf J (ModuleCat.{max u v} R))]
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ J U)
  {Y : Sheaf J (ModuleCat.{max u v} R)} (I : InjectiveResolution Y)

local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.complex J R F
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.augmentation J R F
local notation "A" => Functor.obj (constantSheaf J (ModuleCat R)) (ModuleCat.of R R)

private instance moduleCoproducts (S : Type*) [CommRing S] : HasCoproducts.{0} (ModuleCat.{w} S) :=
  fun T => (ModuleCat.hasColimitsOfSize.{w, _, 0, 0} S).has_colimits_of_shape (Discrete T)

def totalHomologyIso (i : ℕ) :
    ((FrameCech.ExtCoefficientEdge.bicomplex.{u, v, z} F R J I.cocomplex).total (.up ℕ)).homology i ≅
      ModuleCat.of R (Abelian.Ext.{max u v z} A Y i) := by
  let : QuasiIso e := CoveringPresentationResolution.augmentation_quasiIso J R F hcover
  exact HomologicalComplex.homologyMapIso
    (FrameCech.ExtCoefficientEdge.totalIso.{u, v, z} F R J I.cocomplex).symm i ≪≫
      ResolutionHom.Total.homologyIso R P e I i

def homologyIso (I : InjectiveResolution Y)
    (hP : ∀ a q, Subsingleton (Abelian.Ext.{max u v z} ((P).X a) Y (q + 1)))
    (i : ℕ) : (FrameCech.Ext.Comparison.liftedComplex.{u, v, z} F R J Y).homology i ≅
    ModuleCat.of R (Abelian.Ext.{max u v z} A Y i) :=
  letI : QuasiIso e := CoveringPresentationResolution.augmentation_quasiIso J R F hcover
  HomologicalComplex.homologyMapIso
    (FrameCech.Ext.Comparison.comparison.{u, v, z} F R J Y).symm i ≪≫
      ResolutionCohomology.homologyIso R P e I hP i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.FrameCechCohomology
