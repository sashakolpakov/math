import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ConcentrationCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.LocalClass

/-! # Global Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.GlobalNormalization

noncomputable section

/-! The original fixed point coordinate followed by its global pure
class is exactly the native ordered-total coordinate map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
  Survivor.coefficient_qc Survivor.coefficient_finite
variable {X : Scheme.{u}} (i : X ⟶ Proj (homogeneousSubmodule (Fin (n+2)) R))
  [IsClosedImmersion i] (s : Spec (CommRingCat.of R) ⟶ X) [IsClosedImmersion s]
  (hs : s ≫ (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ) = 𝟙 _) (B : ℕ) (hB : n+2 ≤ B)
local notation "π" => OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n+2))
local notation "V" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n+2))
local notation "haV" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) (σ := Fin (n+2))
local notation "hV" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n+2))
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.Survivor.dual i s B

abbrev map := by
  letI : ∀ q, ((D).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc (Survivor.coefficient i s) (Survivor.chart (R := R)) B (n+2) hB
  exact Global.PureSectionClass.map V haV D (n+1) (Survivor.exactAt i s hs B hB) (n+1)

abbrev totalIso := IntrinsicOrdered.CechTransferCoordinates.Intrinsic.iso π V (n+1) D

omit [Module.Injective R R] in
theorem normalization : LocalClass.globalCoordinate i s hs B hB ≫
    map i s hs B hB = (totalIso i s B).hom := by
  let : ∀ q, ((D).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc (Survivor.coefficient i s) (Survivor.chart (R := R)) B (n+2) hB
  have h := Global.PureSectionNormalization.map_eq π V hV haV D (n+1) (Survivor.exactAt i s hs B hB)
  change LocalClass.globalCoordinate i s hs B hB ≫
    Global.PureSectionClass.map V haV D (n+1) (Survivor.exactAt i s hs B hB) (n+1) = _
  rw [h]
  simp only [LocalClass.globalCoordinate, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [ConcentrationCoordinates.concentration]
  exact Iso.hom_inv_id_assoc _ _

omit [Module.Injective R R] in
theorem recovery : LocalClass.globalCoordinate i s hs B hB ≫
    map i s hs B hB ≫ (totalIso i s B).inv = 𝟙 _ := by
  rw [← Category.assoc, normalization, Iso.hom_inv_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.GlobalNormalization
