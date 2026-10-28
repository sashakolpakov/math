import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Descent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Beck Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.BeckDescent

noncomputable section

/-!
# Explicit invariant objects for PoincareBundle descent

The descended module is identified with the equalizer of the coaction
and the adjunction unit. The same equalizer constructs an invariant
sheaf globally. Effectiveness for general geometric pullback is not
assumed by these constructions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Comonad _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The explicit equalizer that imposes the affine descent relation. -/
def moduleInvariants (f : R →+* S) (D : Affine.Descent.ModuleDatum.{u, u} f) : ModuleCat.{u} R :=
  equalizer ((ModuleCat.restrictScalars f).map D.a)
    ((ModuleCat.extendRestrictScalarsAdj f).unit.app _)

/-- Faithfully flat descent identifies its constructed module with the
explicit module of invariants. -/
def moduleInvariantsIso (f : R →+* S) (hf : f.FaithfullyFlat)
    (D : Affine.Descent.ModuleDatum.{u, u} f) :
    moduleInvariants f D ≅ Affine.Descent.descendedModule f hf D :=
  ((ComonadicityInternal.comparisonAdjunction (ModuleCat.extendRestrictScalarsAdj f)).rightAdjointUniq
    (Affine.Descent.descentEquivalence f hf).toAdjunction).app D

/-- The explicit invariant module of a line datum is invertible. -/
theorem moduleInvariants_invertible [IsNoetherianRing R]
    (f : R →+* S) (hf : f.FaithfullyFlat) (D : Affine.Descent.ModuleDatum.{u, u} f)
    [Module.Invertible S D.A] : Module.Invertible R (moduleInvariants f D) := by
  have := Affine.Descent.descendedModule_invertible f hf D
  exact Module.Invertible.congr (moduleInvariantsIso f hf D).symm.toLinearEquiv

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A geometric descent coaction with its counit and cocycle equations. -/
abbrev SheafDatum := (Scheme.Modules.pullbackPushforwardAdjunction f).toComonad.Coalgebra

/-- The globally defined sheaf of invariants. -/
def invariantSheaf (D : SheafDatum f) : Y.Modules :=
  equalizer ((Scheme.Modules.pushforward f).map D.a)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _)

/-- Its inclusion into the direct image of the original module sheaf. -/
def invariantSheafInclusion (D : SheafDatum f) :
    invariantSheaf f D ⟶ (Scheme.Modules.pushforward f).obj D.A :=
  equalizer.ι _ _

/-- Pulling back the invariant sheaf has a canonical comparison with
the original module sheaf, respecting its full descent coaction. -/
def invariantComparison (D : SheafDatum f) :
    (Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)).obj
      (invariantSheaf f D) ⟶ D :=
  (ComonadicityInternal.comparisonAdjunction
    (Scheme.Modules.pullbackPushforwardAdjunction f)).counit.app D

/-- The invariant sheaf has the descent universal property. -/
def invariantHomEquiv (D : SheafDatum f) (N : Y.Modules) :
    ((Comonad.comparison (Scheme.Modules.pullbackPushforwardAdjunction f)).obj N ⟶ D) ≃
      (N ⟶ invariantSheaf f D) :=
  ComonadicityInternal.comparisonRightAdjointHomEquiv
    (Scheme.Modules.pullbackPushforwardAdjunction f) D N

/-- Preservation of the defining equalizer makes the canonical pullback
comparison an isomorphism. This isolates the local verification needed
for effective geometric descent. -/
theorem invariantComparison_isIso_of_preservesEqualizer (D : SheafDatum f)
    [hpres : PreservesLimit
      (parallelPair ((Scheme.Modules.pushforward f).map D.a)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _))
      (Scheme.Modules.pullback f)] : IsIso (invariantComparison f D).f := by
  change IsIso ((ComonadicityInternal.comparisonAdjunction
    (Scheme.Modules.pullbackPushforwardAdjunction f)).counit.app D).f
  rw [ComonadicityInternal.comparisonAdjunction_counit_f]
  change IsIso (IsLimit.conePointUniqueUpToIso (beckEqualizer D)
    (@ComonadicityInternal.counitLimitOfPreservesEqualizer
      _ _ _ _ _ _ (Scheme.Modules.pullbackPushforwardAdjunction f) D inferInstance hpres)).inv
  exact (IsLimit.conePointUniqueUpToIso _ _).isIso_inv

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.BeckDescent
