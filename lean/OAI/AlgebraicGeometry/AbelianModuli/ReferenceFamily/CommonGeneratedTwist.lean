import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicTensor
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicHyperplaneBundle
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedGlobalGeneration
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree

/-! # Common Generated Twist -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonGeneratedTwist

noncomputable section

/-! Two arbitrary algebraic line bundles on the original projective
variety acquire actual finite generating section families after one
common hyperplane twist. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedGlobalGeneration.Dimension

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance commonGeneratedTwist_monoidal : MonoidalCategory V.carrier.Modules :=
  SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory V.carrier
local instance commonGeneratedTwist_integral : IsIntegral V.carrier := V.property
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem commonGeneratedTwist_finiteType (L : HilbertConstruction.Line.Bundles.LineBundle V.carrier) : L.sheaf.IsFiniteType := by
  let D := SheafCohomology.Projective.InvertibleFinitePresentation.invertibleRankOneCover (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L)
  refine { exists_localGeneratorsData := ⟨SheafCohomology.Projective.InvertibleFinitePresentation.rankOneCoverLocalGenerators D, ?_⟩ }
  constructor
  intro i
  exact SheafCohomology.Projective.InvertibleFinitePresentation.rankOneGenerators_finite _ _ (D.frame i)

theorem exists_common_generated_twist (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier) :
    ∃ H : HilbertConstruction.Line.Bundles.LineBundle V.carrier,
      SheafCohomology.Projective.FiniteGlobalGenerators.HasFiniteGlobalGenerators (L.tensor H).sheaf ∧ SheafCohomology.Projective.FiniteGlobalGenerators.HasFiniteGlobalGenerators (K.tensor H).sheaf := by
  let f := V.presentation.projective.embedding
  let : IsClosedImmersion f := V.presentation.projective.closedImmersion
  let : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  let : L.sheaf.IsFiniteType := commonGeneratedTwist_finiteType V L
  let : K.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent K
  let : K.sheaf.IsFiniteType := commonGeneratedTwist_finiteType V K
  obtain ⟨a, ha⟩ := SheafCohomology.Projective.ClosedGlobalGeneration.Dimension.closedProjective_eventually_hasFiniteGlobalGenerators
    (R := ℂ) (σ := Fin (V.ambientDimension + 1)) (X := V.carrier) f L.sheaf 0
  obtain ⟨b, hb⟩ := SheafCohomology.Projective.ClosedGlobalGeneration.Dimension.closedProjective_eventually_hasFiniteGlobalGenerators
    (R := ℂ) (σ := Fin (V.ambientDimension + 1)) (X := V.carrier) f K.sheaf 0
  let d := max a b
  let P := RepresentationTheory.Theta.Geometric.AlgebraicHyperplaneBundle.lineBundleOfInvertible
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := ℂ) (0 : Fin (V.ambientDimension + 1)) d)
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible 0 d)
  let H := P.pullback f
  exact ⟨H, (ha d (le_max_left a b)).of_iso (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso L.sheaf H.sheaf),
    (hb d (le_max_right a b)).of_iso (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso K.sheaf H.sheaf)⟩

theorem finiteGlobalGenerators_numbered_sections (L : HilbertConstruction.Line.Bundles.LineBundle V.carrier)
    (hL : SheafCohomology.Projective.FiniteGlobalGenerators.HasFiniteGlobalGenerators L.sheaf) :
    ∃ (n : ℕ) (s : Fin (n + 1) → (HilbertConstruction.Line.Bundles.structureModule V.carrier ⟶ L.sheaf)),
      ∀ x : V.carrier, ∃ i, x ∈ HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i) := by
  obtain ⟨I, hI, s, hs⟩ := hL.section_cover L
  let : Fintype I := hI
  have hne : Nonempty I := by
    obtain ⟨x⟩ := (inferInstance : Nonempty V.carrier)
    obtain ⟨i, _⟩ := hs x
    exact ⟨i⟩
  let : Nonempty I := hne
  let n := Fintype.card I - 1
  have hn : Fintype.card I = n + 1 := by
    have hpos : 0 < Fintype.card I := Fintype.card_pos
    dsimp [n]
    omega
  let e : I ≃ Fin (n + 1) := (Fintype.equivFin I).trans (finCongr hn)
  refine ⟨n, fun i => s (e.symm i), ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hs x
  refine ⟨e i, ?_⟩
  simpa only [Equiv.symm_apply_apply] using hi

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonGeneratedTwist
