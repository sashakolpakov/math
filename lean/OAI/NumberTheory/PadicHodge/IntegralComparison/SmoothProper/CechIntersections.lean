import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamZariski
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates

/-! # Cech Intersections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechIntersections

noncomputable section

/-!
# IntegralComparison: every actual Čech intersection inherits finite étale coordinates
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover

universe u

variable (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
  [IsProper X.hom] [Smooth X.hom]

local instance separated : IsSeparated (terminal.from X.left) := by
  rw [← terminal.comp_from X.hom]
  infer_instance

variable (q : ℕ) (t : Fin (q + 1) → EtaleCover.Index k X)

def opens : X.left.Opens := ∏ᶜ (DeRhamZariski.opens k X ∘ t)

theorem eq_iInf : opens k X q t = ⨅ j, DeRhamZariski.opens k X (t j) := by
  apply le_antisymm
  · exact le_iInf (fun j => leOfHom (Pi.π (DeRhamZariski.opens k X ∘ t) j))
  · exact leOfHom (Pi.lift (fun j => homOfLE (iInf_le (fun j => DeRhamZariski.opens k X (t j)) j)))

theorem affine : IsAffineOpen (opens k X q t) := by
  rw [eq_iInf]
  exact IsAffineOpen.iInf (fun j => DeRhamZariski.affine k X (t j))

theorem le_chart : opens k X q t ≤ (EtaleCover.chartMap k X (t 0)).opensRange :=
  leOfHom (Pi.π (DeRhamZariski.opens k X ∘ t) 0)

def coordinateRing : CommAlgCat.{u} k := (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op (opens k X q t))

def chartMap : Spec (CommRingCat.of (coordinateRing k X q t)) ⟶ X.left := (affine k X q t).fromSpec

instance chartMap_open : IsOpenImmersion (chartMap k X q t) :=
  IsAffineOpen.isOpenImmersion_fromSpec (affine k X q t)

theorem chartMap_range : (chartMap k X q t).opensRange = opens k X q t :=
  (affine k X q t).opensRange_fromSpec

theorem chartMap_over : chartMap k X q t ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing k X q t))) :=
  AffineOpen.SectionBase.overBase k X (opens k X q t) (affine k X q t)

@[instance_reducible]
def polynomialAlgebra : Algebra (MvPolynomial (EtaleCover.coordinateIndex k X (t 0)) k) (coordinateRing k X q t) :=
  @AffineOpen.EtaleCoordinates.polynomialAlgebra k inferInstance X (opens k X q t) (affine k X q t)
    (EtaleCover.coordinateRing k X (t 0)) inferInstance
    (EtaleCover.chartMap k X (t 0)) (EtaleCover.chartMap_open k X (t 0))
    (le_chart k X q t) (EtaleCover.coordinateIndex k X (t 0)) (EtaleCover.polynomialAlgebra k X (t 0))

theorem etale : letI := polynomialAlgebra k X q t
    Algebra.Etale (MvPolynomial (EtaleCover.coordinateIndex k X (t 0)) k) (coordinateRing k X q t) :=
  @AffineOpen.EtaleCoordinates.etale k inferInstance X (opens k X q t) (affine k X q t)
    (EtaleCover.coordinateRing k X (t 0)) inferInstance
    (EtaleCover.chartMap k X (t 0)) (EtaleCover.chartMap_open k X (t 0))
    (le_chart k X q t) (EtaleCover.coordinateIndex k X (t 0)) (EtaleCover.polynomialAlgebra k X (t 0))
    (EtaleCover.coordinateEtale k X (t 0))

theorem tower : letI := polynomialAlgebra k X q t
    IsScalarTower k (MvPolynomial (EtaleCover.coordinateIndex k X (t 0)) k) (coordinateRing k X q t) :=
  @AffineOpen.EtaleCoordinates.tower k inferInstance X (opens k X q t) (affine k X q t)
    (EtaleCover.coordinateRing k X (t 0)) inferInstance
    (EtaleCover.chartMap k X (t 0)) (EtaleCover.chartMap_open k X (t 0))
    (le_chart k X q t) (EtaleCover.coordinateIndex k X (t 0)) (EtaleCover.polynomialAlgebra k X (t 0))
    (EtaleCover.coordinateAlgebra k X (t 0)) (EtaleCover.coordinateTower k X (t 0)) (EtaleCover.chartMap_over k X (t 0))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechIntersections
