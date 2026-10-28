import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ComplementAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedCoordinateNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ComplementNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.RelativeDimension

/-! # Adjunction Charts -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionCharts

noncomputable section

/-! Genuine affine charts for the adjunction map, including the
complement of the closed subscheme. Smooth projective geometry supplies
a basis of these charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.LocalAdjunction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) (f : X ⟶ IntrinsicOverlap.Intrinsic.model R n)
  [IsClosedImmersion f.left] (g : ℕ)

local instance ambientAlgebra (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) : Algebra R Γ(IntrinsicOverlap.Intrinsic.space R n, U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (IntrinsicOverlap.Intrinsic.model R n) U

structure Data (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U) where
  equations : Fin (n - g) → Γ(IntrinsicOverlap.Intrinsic.space R n, U)
  generates : Koszul.OrientedTopCohomology.ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U) equations = LocalAdjunction.ideal X f U hU
  regular : RingTheory.Sequence.IsWeaklyRegular Γ(IntrinsicOverlap.Intrinsic.space R n, U) (List.ofFn equations)
  conormalBasis : Module.Basis (Fin (n - g)) (LocalAdjunction.quotient X f U hU) (LocalAdjunction.ideal X f U hU).Cotangent
  conormalBasis_apply : ∀ a, conormalBasis a = (LocalAdjunction.ideal X f U hU).toCotangent
    (ConormalKoszulPurity.conormalVectors Γ(IntrinsicOverlap.Intrinsic.space R n, U) (LocalAdjunction.ideal X f U hU) equations generates a)
  quotientBasis : Module.Basis (Fin g) (LocalAdjunction.quotient X f U hU) Ω[LocalAdjunction.quotient X f U hU⁄R]
  coordinateIndex : Type u
  finiteVariables : Fintype coordinateIndex
  coordinates : Algebra (MvPolynomial coordinateIndex R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
  coordinateTower : letI := coordinates
    IsScalarTower R (MvPolynomial coordinateIndex R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))
  coordinateEtale : letI := coordinates
    Algebra.Etale (MvPolynomial coordinateIndex R) (Intrinsic.SmoothClosedSections.ring R X (f.left ⁻¹ᵁ U))

structure Chart (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) where
  affine : IsAffineOpen U
  coordinate : Fin (n + 1)
  le_coordinate : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) coordinate
  description : Sum (PLift (RingHom.ker (f.left.app U).hom = ⊤)) (Data X f g U affine)

def Good (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) : Prop := Nonempty (Chart X f g U)

variable [Smooth X.hom]

def Data.sectionIso {U : (IntrinsicOverlap.Intrinsic.space R n).Opens} {hU : IsAffineOpen U} (D : Data X f g U hU)
    (i : Fin (n + 1)) (hUi : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n) :
    (Affine.ModuleExactSections.sections U).obj ((LocalAdjunction.dual X f j B).homology (n - g)) ≅
      (Affine.ModuleExactSections.sections U).obj
        (Intrinsic.ClosedFormSections.directImage R X (IntrinsicOverlap.Intrinsic.model R n) f g) := by
  let := D.finiteVariables
  let : LinearOrder D.coordinateIndex :=
    LinearOrder.lift' (Fintype.equivFin D.coordinateIndex) (Fintype.equivFin D.coordinateIndex).injective
  let := D.coordinates
  let := D.coordinateTower
  let := D.coordinateEtale
  exact LocalAdjunction.sectionIso X f j B hB U hU i hUi
    (Nat.sub_add_cancel hg) D.equations D.generates D.regular D.conormalBasis D.quotientBasis D.coordinateIndex

def Chart.sectionIso {U : (IntrinsicOverlap.Intrinsic.space R n).Opens} (C : Chart X f g U)
    (j : Fin (n + 1)) (B : ℕ) (hB : n + 1 ≤ B) (hg : g ≤ n) :
    (Affine.ModuleExactSections.sections U).obj ((LocalAdjunction.dual X f j B).homology (n - g)) ≅
      (Affine.ModuleExactSections.sections U).obj
        (Intrinsic.ClosedFormSections.directImage R X (IntrinsicOverlap.Intrinsic.model R n) f g) :=
  match C.description with
  | Sum.inl h => ComplementAdjunction.sectionIso f.left j B (n + 1) hB
      U C.affine C.coordinate C.le_coordinate h.down (n - g) (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X g)
  | Sum.inr D => D.sectionIso X f g C.coordinate C.le_coordinate j B hB hg

omit [Smooth X.hom] in
theorem exists_neighborhood [IsProper X.hom] [SmoothOfRelativeDimension g X.hom]
    (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (y : IntrinsicOverlap.Intrinsic.space R n) (hy : y ∈ U) :
    ∃ (V : (IntrinsicOverlap.Intrinsic.space R n).Opens), IsAffineOpen V ∧ Good X f g V ∧ y ∈ V ∧ V ≤ U := by
  classical
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let : SmoothOfRelativeDimension n (IntrinsicOverlap.Intrinsic.model R n).hom := by
    change SmoothOfRelativeDimension n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)))
    simpa only [Fintype.card_fin, Nat.add_sub_cancel] using
      (RelativeDimension.smooth (R := R) (σ := Fin (n + 1)))
  let : LocallyOfFiniteType (IntrinsicOverlap.Intrinsic.model R n).hom := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
  let : IsLocallyNoetherian (IntrinsicOverlap.Intrinsic.model R n).left := LocallyOfFiniteType.isLocallyNoetherian (IntrinsicOverlap.Intrinsic.model R n).hom
  have hcover : y ∈ ⨆ i : Fin (n + 1), AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i := by
    rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hyi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcover
  by_cases himage : y ∈ Set.range f.left
  · obtain ⟨x, rfl⟩ := himage
    obtain ⟨V, hV, hVU, hxV, τ, hτ, a, hcoords, c, s, hs, hr, bI, hbI, hc, ⟨bQ⟩⟩ :=
      IntegralComparison.Smooth.ClosedCoordinateNeighborhood.exists_neighborhood R X (IntrinsicOverlap.Intrinsic.model R n) f n g
        (U ⊓ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) x ⟨hy, hyi⟩
    subst c
    let D : Data X f g V hV :=
      { equations := s
        generates := hs
        regular := hr.toIsWeaklyRegular
        conormalBasis := bI
        conormalBasis_apply := hbI
        quotientBasis := bQ
        coordinateIndex := τ
        finiteVariables := hτ
        coordinates := a
        coordinateTower := hcoords.1
        coordinateEtale := hcoords.2 }
    exact ⟨V, hV, ⟨⟨hV, i, hVU.trans inf_le_right, Sum.inr D⟩⟩, hxV, hVU.trans inf_le_left⟩
  · obtain ⟨V, hV, hVU, hyV, hunit⟩ := Closed.ComplementNeighborhood.exists_affine f.left
      (U ⊓ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) y ⟨hy, hyi⟩ himage
    exact ⟨V, hV, ⟨⟨hV, i, hVU.trans inf_le_right, Sum.inl ⟨hunit⟩⟩⟩, hyV, hVU.trans inf_le_left⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AdjunctionCharts
