import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.ConcentrationTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.SheafGlobalCohomology

/-! # Supported Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SupportedClass

noncomputable section

/-! The original fixed point trace class has a canonical supported
lift. Extension followed by the original concentration inverse recovers
that same total-cohomology class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem recovery {C : Type*} [Category C] {A B D E : C}
    (e : A ≅ B) (f : D ≅ B) (l : D ⟶ E) (r : E ⟶ D) (h : l ≫ r = 𝟙 D) :
    (e.hom ≫ f.inv ≫ l) ≫ (r ≫ f.hom ≫ e.inv) = 𝟙 A := by
  simp only [Category.assoc]
  rw [← Category.assoc l r, h, Category.id_comp, Iso.inv_hom_id_assoc, Iso.hom_inv_id]

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion i] (s : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s]
  (hs : s ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n + 2 ≤ B)

attribute [local instance] Survivor.coefficient_qc
  Survivor.coefficient_finite

local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.Serre.fixedTower (OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor.coefficient i s) B n (Fintype.card_fin (n+2))
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor.survivor i s B
local notation "π" => OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2))
local notation "V" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2))
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.SupportedSurvivor.single S (n+1)
abbrev outside := SectionIdealPuncturedCover.outside (s ≫ i).ker
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SupportedClass.outside i s

abbrev concentration := ProjectiveTower.ConcentrationTrace.concentration T B n
  (Fintype.card_fin (n+2))
  (ProjectiveRefinement.Serre.fixed_above (Survivor.coefficient i s) B n (Fintype.card_fin (n+2)))
  hB (n+1) (Survivor.exactAt i s hs B hB) 0 (Nat.zero_add _)

abbrev globalIso := Single.SheafGlobalCohomology.iso π V
  (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n+2))) S (n+1)

variable (U : (Proj (homogeneousSubmodule (Fin (n+2)) R)).Opens)
  (hU : ⊤ ≤ (s ≫ i) ⁻¹ᵁ U)

def liftToSupport := (concentration i s hs B hB).hom ≫ (globalIso i s B).inv ≫
  homologyMap (Survivor.lift i s hs B hB U) (n+1)

def extension := Supported.SectionsExcision.extensionComplex O U
  (SectionIdealPuncturedCover.section_global U (s ≫ i) hU) L

def recoverTotal := homologyMap (extension i s B U hU) (n+1) ≫
  (globalIso i s B).hom ≫ (concentration i s hs B hB).inv

omit [Module.Injective R R] in
theorem lift_recover : liftToSupport i s hs B hB U ≫ recoverTotal i s hs B hB U hU = 𝟙 _ :=
  recovery (concentration i s hs B hB) (globalIso i s B)
    (homologyMap (Survivor.lift i s hs B hB U) (n+1))
    (homologyMap (extension i s B U hU) (n+1))
    (Survivor.homology_extension i s hs B hB U hU (n+1))

variable [IsArtinianRing R] [IsLocalRing R]
  [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]
  [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

abbrev fixedPointClass :=
  (Projective.TotalUnitMap.fixedTrace (Survivor.coefficient i s) B n (Fintype.card_fin (n+2)) hB
    (Projective.SectionClass.pointUnitIso i s hs)).inv 1

abbrev supportedPointClass := liftToSupport i s hs B hB U (fixedPointClass i s hs B hB)

omit [IsArtinianRing R] [IsLocalRing R] [IsProper (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [Smooth (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] [GeometricallyConnected (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)] in
theorem fixed_point_recovered : recoverTotal i s hs B hB U hU
    (supportedPointClass i s hs B hB U) = fixedPointClass i s hs B hB :=
  ConcreteCategory.congr_hom (lift_recover i s hs B hB U hU) (fixedPointClass i s hs B hB)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.SupportedClass
