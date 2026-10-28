import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.TorsionCoefficientCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionEvaluationRank
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.CokernelRelabeling
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionStableRankLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MatrixKernelGrassmannian

/-! # Torsion Evaluation Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TorsionEvaluationRank

noncomputable section

/-! The actual high-torsion monomial matrix has flat cokernel of the
prescribed complementary rank over every noetherian coefficient ring.
The proof uses the actual saturated family and O(1) after localization,
then detects flatness and rank with the localized matrices. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {g N n r : ℕ} {δ : Fin g → ℕ} [NeZero n] {P : Polynomial ℚ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R r P)
variable (e : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
variable (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback e.hom.left).sheaf ≅
  (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
variable (hg : 0 < g) (hδ : ∀ j, 0 < δ j) (hN : 3 ≤ N)
variable (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
variable (level : A.abelian.FullLevel n) (D : ℕ) (hD : 0 < D)
variable (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} r P ≤ D)
variable (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < n ^ 2)
variable (w : Multiplicative (Fin (2 * g) → ZMod n) → Fin (r + 1) → R)
variable (i : Multiplicative (Fin (2 * g) → ZMod n) → Fin (r + 1)) (hi : ∀ c, w c (i c) = 1)
variable (hw : ∀ c, (A.abelian.fullLevelGlobalSection level c ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
  AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R (w c) (i c) (hi c))

include A I e eL hg hδ hN hunit level hD hdegree hlarge i hi hw

theorem auxiliaryTorsionMonomialMatrix_localCoefficient_flatRank
    (C : Type u) [CommRing C] [IsNoetherianRing C] [IsLocalRing C] (φ : R →+* C) :
    Module.Flat C ((Multiplicative (Fin (2 * g) → ZMod n) → C) ⧸
      (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix (fun c j => φ (w c j)) D)).range) ∧
    ∀ p : PrimeSpectrum C, Module.rankAtStalk (R := C)
      ((Multiplicative (Fin (2 * g) → ZMod n) → C) ⧸
        (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix (fun c j => φ (w c j)) D)).range) p +
          (P.eval (D : ℚ)).num.toNat = n ^ (2 * g) := by
  let f := Spec.map (CommRingCat.ofHom φ)
  have hunitC : IsUnit (N : Γ(Spec (.of C), ⊤)) := by
    simpa only [map_natCast] using hunit.map f.appTop.hom
  exact Local.TorsionEvaluationRank.localAuxiliaryTorsionMonomialMatrix_flatRank (A.pullback f) (I.coefficientChange φ)
    (Embedded.PolarizedCoefficientChange.embeddedCoefficientChangeIso A I e φ) (Embedded.PolarizedCoefficientChange.embeddedCoefficientChangeTwistingIso A I e φ eL)
    hg hδ hN hunitC (level.pullback f) D hD hdegree hlarge (fun c j => φ (w c j)) i
    (fun c => (congrArg φ (hi c)).trans φ.map_one)
    (fun c => Embedded.TorsionCoefficientCoordinates.embeddedTorsionCoefficientChange_coordinates A I e level φ c (w c) (i c) (hi c) (hw c))

theorem noetherianAuxiliaryTorsionMonomialMatrix_flatRank :
    Module.Flat R ((Multiplicative (Fin (2 * g) → ZMod n) → R) ⧸
      (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix w D)).range) ∧
    ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R)
      ((Multiplicative (Fin (2 * g) → ZMod n) → R) ⧸
        (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix w D)).range) p +
          (P.eval (D : ℚ)).num.toNat = n ^ (2 * g) := by
  let ℓ := Local.TorsionStableRankLift.liftedFullLevelLabelEnumeration (g := g) (n := n)
  let v := fun c => w (ℓ c)
  let F := Configuration.MonomialMatrix.configurationMonomialMatrix v D
  have hF : Module.Flat R ((ULift.{u} (Fin (n ^ (2 * g))) → R) ⧸ (Matrix.toLin' F).range) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R)
        ((ULift.{u} (Fin (n ^ (2 * g))) → R) ⧸ (Matrix.toLin' F).range) p +
          (P.eval (D : ℚ)).num.toNat = Fintype.card (ULift.{u} (Fin (n ^ (2 * g)))) := by
    apply (HilbertConstruction.Matrix.CokernelLocalization.matrixCokernel_flatRank_iff_localizations F (P.eval (D : ℚ)).num.toNat).mpr
    intro p
    let C := Localization.AtPrime p.asIdeal
    let φ := algebraMap R C
    have h := auxiliaryTorsionMonomialMatrix_localCoefficient_flatRank A I e eL hg hδ hN hunit
      level D hD hdegree hlarge w i hi hw C φ
    have he := (Configuration.CokernelRelabeling.configurationMonomialMatrix_flatRank_relabel_iff
      (fun c j => φ (w c j)) D (P.eval (D : ℚ)).num.toNat (n ^ (2 * g)) ℓ).mpr h
    have hmap : F.map φ = Configuration.MonomialMatrix.configurationMonomialMatrix (fun c j => φ (w (ℓ c) j)) D :=
      Configuration.MonomialMatrix.configurationMonomialMatrix_map φ v
    rw [hmap]
    have := HilbertConstruction.Flat.MatrixKernelGrassmannian.matrixCokernel_projective_of_flat
      (Configuration.MonomialMatrix.configurationMonomialMatrix (fun c j => φ (w (ℓ c) j)) D) he.1
    have : Module.Free C ((ULift.{u} (Fin (n ^ (2 * g))) → C) ⧸
        (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix (fun c j => φ (w (ℓ c) j)) D)).range) :=
      Module.free_of_flat_of_isLocalRing
    refine ⟨he.1, ?_⟩
    simpa [Module.rankAtStalk_eq_finrank_of_free] using
      he.2 (IsLocalRing.closedPoint C)
  apply (Configuration.CokernelRelabeling.configurationMonomialMatrix_flatRank_relabel_iff w D (P.eval (D : ℚ)).num.toNat (n ^ (2 * g)) ℓ).mp
  simpa only [Fintype.card_ulift, Fintype.card_fin] using hF

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TorsionEvaluationRank
