import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.ProperTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SectionClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SectionCoefficientUnit

/-! # Section Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionUnit

noncomputable section

/-! The actual finite coefficient quotient onto a lifted section sends
the canonical global unit to the same fixed point unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [IsProper Y.hom] [Smooth Y.hom] [GeometricallyConnected Y.hom]
  (s : Spec (CommRingCat.of R) ⟶ Y.left) (hs : s ≫ Y.hom = 𝟙 _)

local notation "π" => OAI.AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2))

local instance target_proper : IsProper (i.left ≫ π) := by
  change IsProper (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w i]
  infer_instance

local instance target_smooth : Smooth (i.left ≫ π) := by
  change Smooth (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w i]
  infer_instance

local instance target_connected : GeometricallyConnected (i.left ≫ π) := by
  change GeometricallyConnected (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w i]
  infer_instance

local instance source_proper : IsProper (f.left ≫ i.left ≫ π) := by
  change IsProper (f.left ≫ i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w i, Over.w f]
  infer_instance

local instance source_smooth : Smooth (f.left ≫ i.left ≫ π) := by
  change Smooth (f.left ≫ i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w i, Over.w f]
  infer_instance

local instance source_connected : GeometricallyConnected (f.left ≫ i.left ≫ π) := by
  change GeometricallyConnected (f.left ≫ i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom)
  rw [Over.w i, Over.w f]
  infer_instance

include hs in
omit [IsNoetherianRing R] [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [IsProper Y.hom] [Smooth Y.hom] [GeometricallyConnected Y.hom] in
theorem section_over : (s ≫ f.left) ≫ (i.left ≫ π) = 𝟙 _ := by
  change (s ≫ f.left) ≫ (i.left ≫ (Projective.IntrinsicOverlap.Intrinsic.model R (n + 1)).hom) = 𝟙 _
  rw [Category.assoc, Over.w i, Over.w f]
  exact hs

abbrev coefficientUnit := (ProperTraceBase.coefficientUnitIso X Y f i s hs).toLinearEquiv

local notation "U" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2))
local notation "hU" => OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := Fin (n + 2))

omit [IsNoetherianRing R] [Module.Injective R R] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] in
theorem coefficientUnit_one : coefficientUnit X Y f i s hs 1 =
    Cech.StructurePullbackUnit.unit f.left i.left π U hU :=
  IteratedCechStructureUnit.artinianIso_one f.left i.left π s
    (ProperTraceBase.section_over X Y f i s hs) U hU

omit [IsNoetherianRing R] [Module.Injective R R] [IsArtinianRing R] [IsLocalRing R] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] [IsProper Y.hom] [Smooth Y.hom] [GeometricallyConnected Y.hom] in
theorem pointUnit_one :
    Projective.SectionClass.pointUnitIso i.left (s ≫ f.left) (section_over X Y f i s hs) 1 =
      Cech.StructurePullbackUnit.unit (s ≫ f.left) i.left π U hU := by
  let : IsIso ((s ≫ f.left) ≫ i.left ≫ π).appTop := by
    rw [section_over X Y f i s hs]
    infer_instance
  exact IteratedCechStructureUnit.iso_one (s ≫ f.left) i.left π U hU

omit [IsNoetherianRing R] [Module.Injective R R] [Nonempty ↥X.left] [IsFinite (Over.Hom.left f)] [Etale (Over.Hom.left f)] [IsClosedImmersion (Over.Hom.left i)] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] in
theorem unit_preserved :
    (TopCechRightExact.functor π U 0).map
      (Cech.SectionCoefficientUnit.sheafMap s f.left i.left)
      (coefficientUnit X Y f i s hs 1) =
    Projective.SectionClass.pointUnitIso i.left (s ≫ f.left) (section_over X Y f i s hs) 1 := by
  rw [coefficientUnit_one X Y f i s hs, pointUnit_one X Y f i s hs]
  exact Cech.SectionCoefficientUnit.preserves_unit s f.left i.left π U hU

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.SectionUnit
