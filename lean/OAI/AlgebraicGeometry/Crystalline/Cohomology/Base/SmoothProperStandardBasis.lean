import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Chart
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateReindex
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Smooth Proper Standard Basis -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis

noncomputable section

/-! A standard etale basis over any commutative base retains a uniform small coordinate bound from one actual finite cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (k : Type u) [CommRing k] (X : Over (Spec (CommRingCat.of k)))
  [IsProper X.hom] [Smooth X.hom]

def smallCoordinateIndex (i : SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index k X) : Type :=
  Fin (Fintype.card (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i))

instance smallCoordinate_fintype (i : SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index k X) : Fintype (smallCoordinateIndex k X i) :=
  inferInstanceAs (Fintype (Fin _))

instance smallPolynomialAlgebra (i : SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index k X) :
    Algebra (MvPolynomial (smallCoordinateIndex k X i) k) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i) :=
  NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateReindex.algebra k (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i) (smallCoordinateIndex k X i) (Fintype.equivFin _)

instance smallCoordinateTower (i : SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index k X) :
    IsScalarTower k (MvPolynomial (smallCoordinateIndex k X i) k) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i) :=
  NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateReindex.scalarTower k (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i) (smallCoordinateIndex k X i) (Fintype.equivFin _)

instance smallCoordinateEtale (i : SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index k X) :
    Algebra.Etale (MvPolynomial (smallCoordinateIndex k X i) k) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i) :=
  NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateReindex.etale k (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i) (smallCoordinateIndex k X i) (Fintype.equivFin _)

abbrev FirstIndex := Σ i : SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index k X,
  {r : SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i //
    Algebra.IsStandardEtale (MvPolynomial (smallCoordinateIndex k X i) k)
      (Localization.Away r)}

abbrev Index := Σ i : FirstIndex k X, Localization.Away i.2.val

abbrev coordinateIndex (i : Index k X) := smallCoordinateIndex k X i.1.1

def Ring (i : Index k X) : Type u := Localization.Away i.2

instance ringCommRing (i : Index k X) : CommRing (Ring k X i) :=
  inferInstanceAs (CommRing (Localization.Away i.2))

instance coordinateAlgebra (i : Index k X) : Algebra k (Ring k X i) :=
  inferInstanceAs (Algebra k (Localization.Away i.2))

instance polynomialAlgebra (i : Index k X) : Algebra (MvPolynomial (coordinateIndex k X i) k) (Ring k X i) :=
  inferInstanceAs (Algebra (MvPolynomial (coordinateIndex k X i) k) (Localization.Away i.2))

instance coordinateTower (i : Index k X) : IsScalarTower k (MvPolynomial (coordinateIndex k X i) k) (Ring k X i) :=
  inferInstanceAs (IsScalarTower k (MvPolynomial (coordinateIndex k X i) k) (Localization.Away i.2))

instance standard (i : Index k X) : Algebra.IsStandardEtale (MvPolynomial (coordinateIndex k X i) k) (Ring k X i) := by
  let : Algebra.IsStandardEtale (MvPolynomial (coordinateIndex k X i) k) (Localization.Away i.1.2.val) := i.1.2.property
  change Algebra.IsStandardEtale (MvPolynomial (coordinateIndex k X i) k) (Localization.Away i.2)
  exact Algebra.IsStandardEtale.of_isLocalizationAway i.2

def presentation (i : Index k X) : StandardEtalePresentation (MvPolynomial (coordinateIndex k X i) k) (Ring k X i) :=
  Classical.choice inferInstance

def firstMap (i : FirstIndex k X) : Spec (CommRingCat.of (Localization.Away i.2.val)) ⟶ X.left :=
  NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Chart.map (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i.1)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap k X i.1) i.2.val

instance firstMap_open (i : FirstIndex k X) : IsOpenImmersion (firstMap k X i) :=
  @NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Chart.map_open (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i.1) inferInstance X.left
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap k X i.1) i.2.val (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_open k X i.1)

theorem firstMap_over (i : FirstIndex k X) : firstMap k X i ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away i.2.val))) :=
  @NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Chart.over_base k (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i.1)
    inferInstance inferInstance (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateAlgebra k X i.1) X.left
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap k X i.1) i.2.val X.hom (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_over k X i.1)

def chartMap (i : Index k X) : Spec (CommRingCat.of (Ring k X i)) ⟶ X.left :=
  NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Chart.map (Localization.Away i.1.2.val) (firstMap k X i.1) i.2

instance chartMap_open (i : Index k X) : IsOpenImmersion (chartMap k X i) :=
  @NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Chart.map_open (Localization.Away i.1.2.val) inferInstance X.left
    (firstMap k X i.1) i.2 (firstMap_open k X i.1)

theorem chartMap_over (i : Index k X) : chartMap k X i ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap k (Ring k X i))) :=
  NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Chart.over_base k (Localization.Away i.1.2.val) (firstMap k X i.1) i.2 X.hom
    (firstMap_over k X i.1)

def opens (i : Index k X) : X.left.Opens := (chartMap k X i).opensRange

theorem neighborhood (U : X.left.Opens) (x : X.left) (hx : x ∈ U) :
    ∃ i : Index k X, x ∈ opens k X i ∧ opens k X i ≤ U := by
  obtain ⟨i, z, hz⟩ := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.covers k X x
  let : z.asIdeal.IsPrime := z.isPrime
  obtain ⟨r, hr, hs⟩ := Algebra.IsEtaleAt.exists_isStandardEtale
    (R := MvPolynomial (smallCoordinateIndex k X i) k) z.asIdeal
  let j : FirstIndex k X := ⟨i, r, hs⟩
  obtain ⟨y, hy⟩ := NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Chart.lift (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap k X i) r z hr
  have hyx : firstMap k X j y = x := hy.trans hz
  have hyU : firstMap k X j y ∈ U := hyx.symm ▸ hx
  obtain ⟨s, ⟨w, hw⟩, hsub⟩ := NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Chart.neighborhood (Localization.Away r) (firstMap k X j) U y hyU
  exact ⟨⟨j, s⟩, ⟨w, hw.trans hyx⟩, hsub⟩

theorem isBasis : Opens.IsBasis (Set.range (opens k X)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U x hx
  obtain ⟨i, hi, hU⟩ := neighborhood k X U x hx
  exact ⟨opens k X i, ⟨i, rfl⟩, hi, hU⟩

def coordinateBound : ℕ := Finset.univ.sup
  (fun i : SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index k X => Fintype.card (smallCoordinateIndex k X i))

theorem coordinate_le (i : Index k X) : Fintype.card (coordinateIndex k X i) ≤ coordinateBound k X :=
  Finset.le_sup (f := fun j : SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index k X =>
    Fintype.card (smallCoordinateIndex k X j)) (Finset.mem_univ i.1.1)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis
