import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.AcyclicResolution
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.BaseChangeRightExact

/-! # Independent Resolution -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IndependentResolution.Tor

noncomputable section

/-! If an algebra is Tor-independent of a particular module, its
actual scalar extension of a projective resolution resolves that module's
scalar extension, without assuming that the algebra is flat. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FlatExtension OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.BaseChangeRightExact

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (N : ModuleCat.{u} R)

def underlyingDerivedIso (n : ℕ) :
    (((Tor (ModuleCat R) n).obj (ModuleCat.of R S)).obj N) ≅
    (ModuleCat.restrictScalars (algebraMap R S)).obj (((FlatExtension.baseChange R S).leftDerived n).obj N) :=
  DerivedBaseChange.leftDerivedIso (FlatExtension.baseChange R S) (tensorLeft (ModuleCat.of R S))
    (𝟭 (ModuleCat R)) (ModuleCat.restrictScalars (algebraMap R S))
    ((Functor.leftUnitor (tensorLeft (ModuleCat.of R S))) ≪≫ (BaseChangeRightExact.restrictBaseChangeIso R S).symm) N n

variable (hv : ∀ n, IsZero (((Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R S)).obj N))

include hv in
theorem baseChange_derived_isZero (n : ℕ) : IsZero (((FlatExtension.baseChange R S).leftDerived (n + 1)).obj N) := by
  have h := (hv n).of_iso (underlyingDerivedIso R S N (n + 1)).symm
  have hs : Subsingleton ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (((FlatExtension.baseChange R S).leftDerived (n + 1)).obj N)) :=
    ModuleCat.subsingleton_of_isZero (R := R) h
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

def resolution (P : ProjectiveResolution N) : ProjectiveResolution ((FlatExtension.baseChange R S).obj N) :=
  AcyclicResolution.resolution (FlatExtension.baseChange R S) P (baseChange_derived_isZero R S N hv)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IndependentResolution.Tor
