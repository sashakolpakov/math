import OAI.AlgebraicGeometry.FormalGeometry.Completion.LineBundleHilbertLeading
import OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertCokernel
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedMorphismReflection

/-! # Effective Hilbert Difference -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.EffectiveHilbertDifference

noncomputable section

/-! A generated nontrivial line bundle has a positive Hilbert-polynomial
difference from the structure sheaf. The difference has strictly lower degree. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Polynomial

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

def lineBundleHilbertPolynomial (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) : Polynomial ℚ := by
  let : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  let : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
  exact ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f L.sheaf j

def lineBundleHilbertDifference (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) : Polynomial ℚ :=
  lineBundleHilbertPolynomial f L j - lineBundleHilbertPolynomial f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) j

omit [IsIntegral X] in
theorem lineBundleHilbertDifference_eq_zero_of_trivial (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1))
    (e : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) : lineBundleHilbertDifference f L j = 0 := by
  let : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  let : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
  let : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  let : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  exact sub_eq_zero.mpr (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_iso f e j)

theorem lineBundleHilbertPolynomial_leadingCoeff_pos (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    0 < (lineBundleHilbertPolynomial f L j).leadingCoeff := by
  let : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  let : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
  exact ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial_leadingCoeff_pos f L.sheaf j (GeneratedLineBundleFrames.Construction.lineBundle_not_isZero L)

theorem lineBundleHilbertDifference_degree_lt (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    (lineBundleHilbertDifference f L j).degree <
      (lineBundleHilbertPolynomial f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) j).degree := by
  have hL : lineBundleHilbertPolynomial f L j ≠ 0 :=
    leadingCoeff_ne_zero.mp (lineBundleHilbertPolynomial_leadingCoeff_pos f L j).ne'
  have hO : lineBundleHilbertPolynomial f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) j ≠ 0 :=
    leadingCoeff_ne_zero.mp (lineBundleHilbertPolynomial_leadingCoeff_pos f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) j).ne'
  have h := LineBundleHilbertLeading.Construction.lineBundle_hilbert_degree_leadingCoeff f L j
  change (lineBundleHilbertPolynomial f L j).natDegree =
      (lineBundleHilbertPolynomial f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) j).natDegree ∧
    (lineBundleHilbertPolynomial f L j).leadingCoeff =
      (lineBundleHilbertPolynomial f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) j).leadingCoeff at h
  exact degree_sub_lt_right (by rw [degree_eq_natDegree hL, degree_eq_natDegree hO, h.1]) hO h.2

theorem lineBundleHilbertDifference_leadingCoeff_pos
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) (hgen : Frame.SectionDetection.Construction.HasFrameSections L.sheaf)
    (hnt : ¬ Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) :
    0 < (lineBundleHilbertDifference f L j).leadingCoeff := by
  let : L.sheaf.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  let : L.sheaf.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
  let : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  let : (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X).IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  obtain ⟨s, hs⟩ := hgen (genericPoint X)
  have : Mono s := IntegralSectionMono.Construction.integral_section_mono_of_nonempty_nonvanishing s ⟨genericPoint X, hs⟩
  let g : ClosedHilbertNumerics.Construction.coherentClosedDirectImage f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ⟶ ClosedHilbertNumerics.Construction.coherentClosedDirectImage f L.sheaf :=
    (Scheme.Modules.pushforward f).map s
  have : Mono g := (Scheme.Modules.pushforward f).map_mono s
  have : (cokernel g).IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel g
  have : (cokernel g).IsFiniteType := SheafCohomology.Projective.CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel g
  have hD : ¬ IsZero (cokernel g) := by
    intro h
    have : Epi g := Preadditive.epi_of_isZero_cokernel g h
    have : Epi s := ClosedMorphismReflection.Construction.moduleMap_epi_of_pushforward_epi f f.isClosedEmbedding.isEmbedding.isInducing s
    have : IsIso s := isIso_of_mono_of_epi s
    exact hnt ⟨(asIso s).symm⟩
  have he := HilbertCokernel.Construction.projectiveCokernelHilbertPolynomial_eq_sub g j
  change Projective.Numerics.Construction.projectiveHilbertPolynomial (cokernel g) j = lineBundleHilbertDifference f L j at he
  rw [← he]
  exact HilbertPositivity.Construction.projectiveHilbertPolynomial_leadingCoeff_pos (cokernel g) j hD

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.EffectiveHilbertDifference
