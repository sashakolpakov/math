import OAI.NumberTheory.PadicHodge.IntegralComparison.Projectivity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.CrystallineFrobenius

/-! # Interfaces -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Interfaces

noncomputable section

/-!
# IntegralComparison: geometric and cohomological names for the source statement

Every name below reuses an independently constructed object. Projectivity
is an actual closed immersion into Proj; cohomology is the original Ext
construction; both Frobenius maps are induced by actual scheme maps.
Finite dimensionality and characteristic-polynomial comparison are not
assumed or encoded in these definitions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

abbrev ProjectiveOver {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) : Prop := Projectivity.Construction.ProjectiveOver k f

instance overMk_isSeparated {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f] : IsSeparated (Over.mk f).hom :=
  inferInstanceAs (IsSeparated f)

/-- The original rational crystalline cohomology, with its Witt fraction-field action. -/
abbrev CrystallineCohomology (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [Fintype k] [CharP k p]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (i : ℕ) :=
  Witt.Crystalline.rationalCohomology p k (Over.mk f) i

/-- Rational pro-étale cohomology of the actual geometric fibre. -/
abbrev EtaleCohomology (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (i : ℕ) :=
  Cohomology.RationalEllAdicCohomology ℓ
    (Frobenius.Geometry.geometricFiber (L := AlgebraicClosure k) f) i

/-- Actual q-Frobenius on the original small crystalline cohomology.
Properness in IntegralComparison supplies the separatedness needed by the proved site comparison. -/
def crystallineQFrobenius (p a : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [Fintype k] [CharP k p]
    (hcard : Fintype.card k = p ^ a)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f] (i : ℕ) :
    CrystallineCohomology p k f i →ₗ[FractionRing (WittVector p k)] CrystallineCohomology p k f i :=
  Global.CrystallineFrobenius.rationalFrobenius p k (Over.mk f) a hcard i

/-- Actual geometric Frobenius, with the inverse q-power field-automorphism convention. -/
def etaleGeometricFrobenius (ℓ p a : ℕ) [Fact ℓ.Prime] [Fact p.Prime]
    (k : Type u) [Field k] [Fintype k] [CharP k p]
    (hcard : Fintype.card k = p ^ a)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (i : ℕ) :
    EtaleCohomology ℓ k f i →ₗ[ℚ_[ℓ]] EtaleCohomology ℓ k f i :=
  (Etale.Frobenius.geometricFrobeniusLinear ℓ p a k hcard f i).toLinearMap

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Interfaces
