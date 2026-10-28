import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FreeNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis

/-! # Trace Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis

noncomputable section

/-! An actual basis of affine opens with étale coordinates and free
finite étale inverse-image algebras, over an arbitrary commutative base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

open OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FreeNeighborhood

universe u

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left]

def HasCoordinates (U : Y.left.Opens) : Prop :=
  ∃ (σ : Type u) (_ : Fintype σ) (a : Algebra (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)),
    letI := a
    IsScalarTower R (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U) ∧
      Algebra.Etale (MvPolynomial σ R) (AffineOpen.DeRhamTrace.targetRing R Y U)

def Good (U : Y.left.Opens) : Prop :=
  IsAffineOpen U ∧ HasCoordinates R Y U ∧ FreeNeighborhood.IsFreeOn R X Y f U

abbrev Index := {U : Y.left.Opens // Good R X Y f U}

abbrev opens (i : Index R X Y f) : Y.left.Opens := i.val

instance affine (i : Index R X Y f) : Fact (IsAffineOpen (opens R X Y f i)) := ⟨i.property.1⟩

instance sectionAlgebra (i : Index R X Y f) :
    Algebra (AffineOpen.DeRhamTrace.targetRing R Y (opens R X Y f i)) (AffineOpen.DeRhamTrace.sourceRing R X Y f (opens R X Y f i)) :=
  AffineOpen.DeRhamTrace.sectionAlgebra R X Y f (opens R X Y f i)

instance sourceFree (i : Index R X Y f) :
    Module.Free (AffineOpen.DeRhamTrace.targetRing R Y (opens R X Y f i)) (AffineOpen.DeRhamTrace.sourceRing R X Y f (opens R X Y f i)) :=
  i.property.2.2

instance sourceFinite (i : Index R X Y f) :
    Module.Finite (AffineOpen.DeRhamTrace.targetRing R Y (opens R X Y f i)) (AffineOpen.DeRhamTrace.sourceRing R X Y f (opens R X Y f i)) :=
  f.left.finite_app _ i.property.1

def coordinateIndex (i : Index R X Y f) : Type u := i.property.2.1.choose

instance coordinateFintype (i : Index R X Y f) : Fintype (coordinateIndex R X Y f i) :=
  i.property.2.1.choose_spec.choose

instance polynomialAlgebra (i : Index R X Y f) :
    Algebra (MvPolynomial (coordinateIndex R X Y f i) R) (AffineOpen.DeRhamTrace.targetRing R Y (opens R X Y f i)) :=
  i.property.2.1.choose_spec.choose_spec.choose

instance coordinateTower (i : Index R X Y f) :
    IsScalarTower R (MvPolynomial (coordinateIndex R X Y f i) R) (AffineOpen.DeRhamTrace.targetRing R Y (opens R X Y f i)) :=
  i.property.2.1.choose_spec.choose_spec.choose_spec.1

instance coordinateEtale (i : Index R X Y f) :
    Algebra.Etale (MvPolynomial (coordinateIndex R X Y f i) R) (AffineOpen.DeRhamTrace.targetRing R Y (opens R X Y f i)) :=
  i.property.2.1.choose_spec.choose_spec.choose_spec.2

@[instance_reducible]
def coordinateOrder (i : Index R X Y f) : LinearOrder (coordinateIndex R X Y f i) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

variable [IsProper Y.hom] [Smooth Y.hom]

theorem neighborhood (U : Y.left.Opens) (x : Y.left) (hx : x ∈ U) :
    ∃ i : Index R X Y f, x ∈ opens R X Y f i ∧ opens R X Y f i ≤ U := by
  obtain ⟨i, hxi, hiU⟩ := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis.neighborhood R Y U x hx
  let C := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis.Ring R Y i
  let g := AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis.chartMap R Y i
  have hW : IsAffineOpen (AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis.opens R Y i) :=
    isAffineOpen_opensRange g
  obtain ⟨V, hxV, hVW, hV, hfree⟩ := FreeNeighborhood.exists_subopen R X Y f
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis.opens R Y i) hW x hxi
  let σ := ULift.{u} (AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis.coordinateIndex R Y i)
  let e : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis.coordinateIndex R Y i ≃ σ := Equiv.ulift.symm
  let : Algebra (MvPolynomial σ R) C := IntegralComparison.Etale.CoordinateReindex.algebra R C
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis.coordinateIndex R Y i) σ e
  let : IsScalarTower R (MvPolynomial σ R) C := IntegralComparison.Etale.CoordinateReindex.scalarTower R C
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis.coordinateIndex R Y i) σ e
  let : Algebra.Etale (MvPolynomial σ R) C := IntegralComparison.Etale.CoordinateReindex.etale R C
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis.coordinateIndex R Y i) σ e
  have hcoord : HasCoordinates R Y V := by
    refine ⟨σ, inferInstance, AffineOpen.EtaleCoordinates.polynomialAlgebra R Y V hV C g hVW σ, ?_⟩
    exact ⟨AffineOpen.EtaleCoordinates.tower R Y V hV C g hVW σ
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperStandardBasis.BaseSmoothProperStandardBasis.chartMap_over R Y i),
      AffineOpen.EtaleCoordinates.etale R Y V hV C g hVW σ⟩
  exact ⟨⟨V, hV, hcoord, hfree⟩, hxV, hVW.trans hiU⟩

theorem isBasis : Opens.IsBasis (Set.range (opens R X Y f)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U x hx
  obtain ⟨i, hi, hU⟩ := neighborhood R X Y f U x hx
  exact ⟨opens R X Y f i, ⟨i, rfl⟩, hi, hU⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasis
