import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperAffineCharts
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Proper Cech Intersections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCechIntersections.CrystallineProperCechIntersections

noncomputable section

/-!
# Every Čech intersection of the proper affine cover has finite coordinates

Properness gives a finite affine cover and separatedness makes every
nonempty finite intersection of its members affine. These are the actual
opens occurring in the Čech complex, with their original maps to the
special fibre and their constructed finite-type coordinate rings.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]

abbrev Index := ProperAffineCharts.CrystallineProperAffineCharts.Index k X

def opens (i : Index k X) : X.left.Opens :=
  (ProperAffineCharts.CrystallineProperAffineCharts.inclusion k X i).left.opensRange

theorem covering : iSup (opens k X) = ⊤ := ProperAffineCharts.CrystallineProperAffineCharts.covering k X

local instance separated : IsSeparated (terminal.from X.left) := by
  rw [← terminal.comp_from X.hom]
  infer_instance

theorem affine_open (i : Index k X) : IsAffineOpen (opens k X i) := by
  have : IsAffine (ProperAffineCharts.CrystallineProperAffineCharts.chart k X i).left := by
    change IsAffine (Spec (CommRingCat.of (ProperAffineCharts.CrystallineProperAffineCharts.coordinateRing k X i)))
    infer_instance
  exact isAffineOpen_opensRange (ProperAffineCharts.CrystallineProperAffineCharts.inclusion k X i).left

variable (n : ℕ) (t : Fin (n + 1) → Index k X)

def intersection : X.left.Opens := ∏ᶜ (opens k X ∘ t)

theorem intersection_eq_iInf : intersection k X n t = ⨅ j, opens k X (t j) := by
  apply le_antisymm
  · exact le_iInf (fun j => leOfHom (Pi.π (opens k X ∘ t) j))
  · exact leOfHom (Pi.lift (fun j => homOfLE (iInf_le (fun j => opens k X (t j)) j)))

theorem intersection_affineOpen : IsAffineOpen (intersection k X n t) := by
  rw [intersection_eq_iInf]
  exact IsAffineOpen.iInf (fun j => affine_open k X (t j))

instance intersection_affine : IsAffine (intersection k X n t).toScheme :=
  intersection_affineOpen k X n t

def coordinateRing : CommRingCat.{u} := Γ((intersection k X n t).toScheme, ⊤)

def chartIso : (intersection k X n t).toScheme ≅ Spec (coordinateRing k X n t) :=
  (intersection k X n t).toScheme.isoSpec

def chartMap : Spec (coordinateRing k X n t) ⟶ X.left :=
  (chartIso k X n t).inv ≫ (intersection k X n t).ι

instance chartMap_open : IsOpenImmersion (chartMap k X n t) := by
  unfold chartMap
  infer_instance

theorem chartMap_range : (chartMap k X n t).opensRange = intersection k X n t :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Scheme.Opens.opensRange_ι _)

instance coordinateAlgebra : Algebra k (coordinateRing k X n t) :=
  (Spec.preimage (chartMap k X n t ≫ X.hom)).hom.toAlgebra

theorem chartMap_over : chartMap k X n t ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing k X n t))) :=
  (Spec.map_preimage _).symm

instance coordinate_finiteType : Algebra.FiniteType k (coordinateRing k X n t) := by
  have h : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing k X n t)))) := by
    rw [← chartMap_over]
    infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h

def chart : Over (Spec (CommRingCat.of k)) :=
  AffineFrameCover.CrystallineAffineFrameCover.affineScheme k (coordinateRing k X n t)

def inclusion : chart k X n t ⟶ X := Over.homMk (chartMap k X n t) (chartMap_over k X n t)

instance inclusion_open : IsOpenImmersion (inclusion k X n t).left := chartMap_open k X n t

variable (p : ℕ) [Fact p.Prime] [CharP k p]

def integralComparison (q : ℕ) :
    (Finite.Affine.FiniteAffineCrystalline.complex p k (coordinateRing k X n t)).homology q ≅
      ModuleCat.of (Site.CoefficientRing p k)
        (Site.integralCohomology p k (chart k X n t) q) :=
  Finite.Affine.FiniteAffineCrystalline.homologyIso p k (coordinateRing k X n t) q

def rationalComparison [PerfectRing k p] (q : ℕ) :
    (Cohomology.Affine.RationalComparison.AffineRationalCrystallineComparison.complex p k (coordinateRing k X n t)).homology q ≅
      Site.rationalCohomology p k (chart k X n t) q :=
  Cohomology.Affine.RationalComparison.AffineRationalCrystallineComparison.homologyIso p k (coordinateRing k X n t) q

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCechIntersections.CrystallineProperCechIntersections
