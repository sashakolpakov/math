import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRResidueRegularSteinberg
import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # DVR Residue Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DVRResidueNaturality.BundleCycles

noncomputable section

/-!
# LineBundleCycles: residue quotients under actual local-ring isomorphisms

Compatible local-ring and fraction-field isomorphisms preserve the
existing integer order and the characterized balanced unit. The actual
induced residue-field map consequently preserves the residue quotient.
The two local uniformizers may be chosen independently.
-/

variable {R S K L : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
variable [Field K] [Field L] [Algebra R K] [Algebra S L] [IsFractionRing R K] [IsFractionRing S L]
variable (e : R ≃+* S) (φ : K ≃+* L)
variable (hφ : ∀ a : R, φ (algebraMap R K a) = algebraMap S L (e a))

include hφ

theorem fractionFieldOrder_equiv (g : K) : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder S (φ g) = SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R g :=
  congrArg (fun z : WithZero (Multiplicative ℤ) => Multiplicative.toAdd (z.unzeroD 1))
    (RationalDivisorRestriction.BundleCycles.ringOrderFrac_equiv e φ hφ g)

theorem dvrBalancedUnit_equiv (π : R) (hπ : Irreducible π) (ρ : S) (hρ : Irreducible ρ) (g h : Kˣ) :
    Units.map e.toMonoidHom (DVRResidueOf.BundleCycles.dvrBalancedUnit π hπ g h) =
      DVRResidueOf.BundleCycles.dvrBalancedUnit ρ hρ (Units.map φ.toMonoidHom g) (Units.map φ.toMonoidHom h) := by
  apply Units.ext
  apply IsFractionRing.injective S L
  change algebraMap S L (e (DVRResidueOf.BundleCycles.dvrBalancedUnit π hπ g h : R)) = _
  have he := congrArg φ (DVRResidueOf.BundleCycles.dvrBalancedUnit_fraction π hπ g h)
  rw [hφ, map_div₀, map_zpow₀, map_zpow₀] at he
  refine he.trans ?_
  rw [DVRResidueOf.BundleCycles.dvrBalancedUnit_fraction ρ hρ]
  change φ (g : K) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (h : K) / φ (h : K) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) =
    φ (g : K) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder S (φ (h : K)) / φ (h : K) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder S (φ (g : K))
  rw [fractionFieldOrder_equiv e φ hφ, fractionFieldOrder_equiv e φ hφ]

/-- The canonical residue-field map transports the actual residue quotient. -/
theorem dvrResidueQuotient_equiv (π : R) (hπ : Irreducible π) (ρ : S) (hρ : Irreducible ρ) (g h : Kˣ) :
    Units.map (IsLocalRing.ResidueField.map (e : R →+* S)).toMonoidHom (DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h) =
      DVRResidueOf.BundleCycles.dvrResidueQuotient ρ hρ (Units.map φ.toMonoidHom g) (Units.map φ.toMonoidHom h) := by
  apply Units.ext
  change IsLocalRing.ResidueField.map (e : R →+* S)
      (IsLocalRing.residue R (DVRResidueOf.BundleCycles.dvrBalancedUnit π hπ g h : R)) =
    IsLocalRing.residue S
      (DVRResidueOf.BundleCycles.dvrBalancedUnit ρ hρ (Units.map φ.toMonoidHom g) (Units.map φ.toMonoidHom h) : S)
  rw [IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue S) (congrArg Units.val (dvrBalancedUnit_equiv e φ hφ π hπ ρ hρ g h))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DVRResidueNaturality.BundleCycles
