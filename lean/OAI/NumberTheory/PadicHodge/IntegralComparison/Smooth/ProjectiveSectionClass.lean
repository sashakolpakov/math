import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSectionClassData

/-! # Projective Section Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSectionClass

noncomputable section

/-! The scalar point class has trace one under the original proper
top-form trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem replace_unit {A B : Type*} [One B] (F : A → B)
    {a b : A} (h : a = b) (hF : F a = 1) : F b = 1 := h ▸ hF

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X : Over (Spec (CommRingCat.of R))) [Nonempty X.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
  (B : ℕ) (hB : n + 2 ≤ B) (g : ℕ) [SmoothOfRelativeDimension g X.hom]

attribute [local instance] ProjectiveSectionClassData.composite_smooth ProjectiveFormTrace.composite_dimension
  ProjectiveFormTrace.composite_proper ProjectiveFormTrace.composite_connected

local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass.scalar i.left
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass.point i.left s
local notation "hn" => Fintype.card_fin (n + 2)
local notation "π" => OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))
local notation "hsec" => OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSectionClassData.section_over X i s hs

theorem pure_trace_one :
    ProjectivePureTrace.trace i.left B n hn hB g
      (ProjectiveSectionClassData.pureClass X i s hs B hB g) = 1 := by
  let : Subsingleton (Spec (.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  let : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id (i.left ≫ π) s hsec
  let : (P).IsQuasicoherent := Finite.MapPureTrace.coefficients_quasicoherent s i.left
  let : (P).IsFiniteType := Finite.MapPureTrace.coefficients_finiteType s i.left
  have h := Projective.UnitPureClass.trace_one M P B n hn hB
    (Cech.StructurePullbackUnit.sheafMap s i.left)
    (Projective.SectionClass.scalarUnitIso i.left s hsec)
    (Projective.SectionClass.pointUnitIso i.left s hsec)
    (Projective.SectionClass.unit_preserved i.left s hsec)
    (n + 1 - g) (ProjectiveSerre.exactAt i.left B n hn hB g) g (ProjectiveSectionClassData.degree X i g)
  exact replace_unit
    (fun v => SerreUnitTrace.trace (Projective.TopTracePairing.coefficientRing R)
      (ProjectivePureTrace.pairing i.left B n hn hB g) v
      (ProjectiveSectionClassData.pureClass X i s hs B hB g))
    (ProjectiveSectionClassData.scalarUnit_one X i s hs) h

theorem trace_one :
    ProjectiveFormTrace.trace X i B hB g (ProjectiveSectionClassData.sectionClass X i s hs B hB g) = 1 := by
  let H := ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := Fin (n + 2)) g
  let e := ProjectiveFormTrace.adjunctionIso X i B hB g
  let x := ProjectiveSectionClassData.pureClass X i s hs B hB g
  have hx := ConcreteCategory.congr_hom (H.mapIso e).hom_inv_id x
  change H.map e.inv (H.map e.hom x) = x at hx
  change ProjectivePureTrace.trace i.left B n hn hB g
    (H.map e.inv (H.map e.hom x)) = 1
  rw [hx]
  exact pure_trace_one X i s hs B hB g

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ProjectiveSectionClass
