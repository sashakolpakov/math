import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DerivedScalarExtension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfacePrimeEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportTor
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Support Tor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.SupportTor

noncomputable section

/-! Native Tor intersection lengths are unchanged when the ambient
map is flat and the induced map of reduced support rings is etale. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension

theorem self_length (R : Type) [CommRing R] (M N : ModuleCat R) (i : ℕ) :
    Module.length R (((Tor (ModuleCat R) i).obj ((ProjectionFormula.Flat.Extension.baseChange R R).obj M)).obj N) =
      Module.length R (((Tor (ModuleCat R) i).obj M).obj N) := by
  let e : (ProjectionFormula.Flat.Extension.baseChange R R).obj M ≅ M := (TensorProduct.lid R M).toModuleIso
  exact Open.SupportTor.length_iso R e (Iso.refl N) i

theorem quotient_self_length (R T : Type) [CommRing R] [CommRing T] [Algebra R T]
    (hRT : Function.Surjective (algebraMap R T)) (M : ModuleCat R) (i : ℕ) :
    Module.length T (((ProjectionFormula.Flat.Extension.baseChange R T).leftDerived i).obj M) =
      Module.length R (((Tor (ModuleCat R) i).obj M).obj (.of R T)) :=
  (DerivedScalarExtension.quotient_length R R T hRT M i).symm.trans (self_length R M (.of R T) i)

variable (R S T U : Type) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [IsLocalRing T] [IsLocalRing U]
  [Algebra R S] [Algebra R T] [Algebra S U] [Algebra T U] [Algebra R U]
  [IsScalarTower R S U] [IsScalarTower R T U] [Module.Flat R S] [Module.Flat T U]
  [IsLocalHom (algebraMap T U)]
  (hRT : Function.Surjective (algebraMap R T)) (hSU : Function.Surjective (algebraMap S U))

include hRT hSU

theorem length (hmax : (IsLocalRing.maximalIdeal T).map (algebraMap T U) = IsLocalRing.maximalIdeal U)
    (M : ModuleCat R) (i : ℕ) :
    Module.length S (((Tor (ModuleCat S) i).obj ((ProjectionFormula.Flat.Extension.baseChange R S).obj M)).obj (.of S U)) =
      Module.length R (((Tor (ModuleCat R) i).obj M).obj (.of R T)) := by
  calc
    _ = Module.length U (((ProjectionFormula.Flat.Extension.baseChange R U).leftDerived i).obj M) :=
      DerivedScalarExtension.quotient_length R S U hSU M i
    _ = Module.length T (((ProjectionFormula.Flat.Extension.baseChange R T).leftDerived i).obj M) *
        Module.length U (U ⧸ (IsLocalRing.maximalIdeal T).map (algebraMap T U)) := by
      rw [(DerivedScalarExtension.derivedIso R T U M i).toLinearEquiv.length_eq]
      exact IsLocalRing.length_baseChange T U _
    _ = Module.length T (((ProjectionFormula.Flat.Extension.baseChange R T).leftDerived i).obj M) := by
      rw [hmax, SurfacePrimeEuler.residue_quotient_length, mul_one]
    _ = _ := quotient_self_length R T hRT M i

theorem euler [Algebra.EssFiniteType T U] [Algebra.FormallyUnramified T U]
    (M : ModuleCat R) (d : ℕ) :
    ProjectionFormula.Tor.Euler.euler S ((ProjectionFormula.Flat.Extension.baseChange R S).obj M) (.of S U) d = ProjectionFormula.Tor.Euler.euler R M (.of R T) d := by
  unfold ProjectionFormula.Tor.Euler.euler ExactLength.rationalLength
  simp_rw [SupportTor.length R S T U hRT hSU Algebra.FormallyUnramified.map_maximalIdeal]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.SupportTor
