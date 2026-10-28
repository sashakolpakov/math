import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallSmoothness
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallPELOrbits
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.BallQuotient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.ProjectiveComponent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HermitianArithmetic

/-! # Ball Projective Components -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallProjectiveComponents

noncomputable section

/-! The full ball through an original PEL object gives its actual
projective component. The arithmetic lattice, Hermitian form, and level
are those of that object throughout the covering construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Topology

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s}
    {iota : E →+* K} {κ : K →+* ℂ}

namespace FinePELModel

attribute [local implicit_reducible] Models.FinePELModel.complexFiber

variable [NeZero N]
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    {A : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ)))}
    {hs : 0 < s} {hdegree : Module.finrank ℚ E = 2 * s}
    (D : Intrinsic.BallCoordinateData.NativeBallCoordinateData A hs hdegree) (hP : P.IsAdmissible)
    (hκ : κ.comp iota = P.μ)

local notation "H" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree
  A.rosati P.normalizedImaginaryScalar
local notation "Λ" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice A.polarized.abelian
  (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) A.action s hs rfl hdegree
local notation "R₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.BallQuotient.HermitianBall.orbitSetoid P H D.normalizer D.hermitian
  P.normalizedImaginaryScalar (And.left (And.right (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP)))
  (And.left (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP)) Λ N
local notation "q₀" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.BallQuotient.HermitianBall.orbitProjection P H D.normalizer D.hermitian
  P.normalizedImaginaryScalar (And.left (And.right (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP)))
  (And.left (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP)) Λ N

include hκ

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallPoint_eq_iff_principalOrbit (hN : 3 ≤ N) (z w : P.Domain) :
    M.realBallPoint hM κ D hP z = M.realBallPoint hM κ D hP w ↔
      ∃ g ∈ (Groups.principalLatticeSubgroup (R := E) (Submodule.toAddSubgroup Λ) N ⊓
        Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)),
        w.val = P.lineActionVia D.normalizer g z.val := by
  change (M.complexPointClassEquiv κ hM).symm _ =
    (M.complexPointClassEquiv κ hM).symm _ ↔ _
  exact (M.complexPointClassEquiv κ hM).symm.injective.eq_iff.trans
    ((PEL.Objects.PELObject.classOf_eq_iff _ _).trans
      (BallPELOrbits.RealBallPELOrbits.iso_iff_principal_orbit A hs hdegree D hP z w hκ hN))

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallOrbitMap (hN : 3 ≤ N) : Quotient R₀ → M.ComplexPoints κ :=
  Quotient.lift (M.realBallPoint hM κ D hP) (fun z w h =>
    (M.realBallPoint_eq_iff_principalOrbit hM κ D hP hκ hN z w).mpr
      ((Hermitian.BallQuotient.HermitianBall.orbitSetoid_iff P H D.normalizer D.hermitian
        P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1
        (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1 Λ N z w).mp h))

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallOrbitMap_projection (hN : 3 ≤ N) (z : P.Domain) :
    M.realBallOrbitMap hM κ D hP hκ hN (q₀ z) = M.realBallPoint hM κ D hP z := rfl

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallOrbitMap_injective (hN : 3 ≤ N) :
    Function.Injective (M.realBallOrbitMap hM κ D hP hκ hN) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h z =>
    induction y using Quotient.inductionOn with
    | h w =>
      intro h
      apply Quotient.sound
      exact (Hermitian.BallQuotient.HermitianBall.orbitSetoid_iff P H D.normalizer D.hermitian
        P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1
        (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1 Λ N z w).mpr
          ((M.realBallPoint_eq_iff_principalOrbit hM κ D hP hκ hN z w).mp h)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallOrbitMap_range (hN : 3 ≤ N) :
    Set.range (M.realBallOrbitMap hM κ D hP hκ hN) =
      Set.range (M.realBallPoint hM κ D hP) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | h z => exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨q₀ z, rfl⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBall_lift_derivative
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ M.complexFiber κ) [Mono f]
    (hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2)
    (q : P.Domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hq : ∀ z, q z ≫ f = M.realBallPoint hM κ D hP z) (z : P.Domain) :
    MDifferentiableAt (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart))
        (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ)) q z ∧
      Function.Bijective (mfderiv (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart))
        (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ)) q z) := by
  obtain ⟨e, he, hez, hhol, _, hrec⟩ :=
    M.exists_native_realBall_moduli_chart hM κ D hP f z (q z) (hq z) hκ hdim
  apply Principal.ProjectiveComponent.localInverseChart_derivative P.domainOpen q z e he hez hhol
  intro w hw
  obtain ⟨hp, hpoint⟩ := hrec (e.symm w.val) (e.map_target hw)
  have heq : (⟨e (e.symm w.val), hp⟩ : P.domain) = w := Subtype.ext (e.right_inv hw)
  rw [heq] at hpoint
  exact (cancel_mono f).mp ((hq w).trans hpoint.symm)

variable [NumberField K] [LocallyOfFiniteType M.space.hom] [QuasiCompact M.space.hom]

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallOrbitMap_continuous (hN : 3 ≤ N) :
    Continuous (M.realBallOrbitMap hM κ D hP hκ hN) :=
  (M.realBallPoint_continuous hM κ D hP hκ hN).quotient_lift _

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallOrbitMap_isOpenEmbedding (hN : 3 ≤ N) :
    Topology.IsOpenEmbedding (M.realBallOrbitMap hM κ D hP hκ hN) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (M.realBallOrbitMap_continuous hM κ D hP hκ hN)
    (M.realBallOrbitMap_injective hM κ D hP hκ hN)
  exact (Hermitian.BallQuotient.HermitianBall.orbitProjection_isOpenQuotientMap P H D.normalizer D.hermitian
    P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1
    (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1 Λ N).isOpenMap_iff.mpr
      (M.realBallPoint_isOpenMap hM κ D hP hκ hN)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.realBallImage_compact (hN : 3 ≤ N)
    (han : ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Datum.RankThreePELDatum.matrixHermitian H v v = 0 → v = 0) :
    IsCompact (Set.range (M.realBallPoint hM κ D hP)) := by
  have : CompactSpace (Quotient R₀) :=
    Hermitian.BallQuotient.HermitianBall.orbitQuotient_compact P H D.normalizer D.hermitian
      P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1
      (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1 Λ N hP
      (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix_symmetry A.polarized A.action s hs rfl hdegree A.rosati
        P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1)
      (Intrinsic.HermitianNondegenerate.IntrinsicHermitianMarking.markedHermitianMatrix_det_ne_zero A.polarized A.action s hs rfl hdegree A.rosati
        P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1)
      (Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice_full_stable A.polarized.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized)
        A.action s hs rfl hdegree) han (NeZero.ne N)
  rw [← M.realBallOrbitMap_range hM κ D hP hκ hN]
  exact isCompact_range (M.realBallOrbitMap_continuous hM κ D hP hκ hN)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.arithmetic_uniformization_of_realBall_image
    (hN : 3 ≤ N)
    (han : ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Datum.RankThreePELDatum.matrixHermitian H v v = 0 → v = 0)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : X.toOver ⟶ M.complexFiber κ)
    [IsOpenImmersion f.left] (hdim : X.complexDimension = 2)
    (hrange : Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) = Set.range (M.realBallPoint hM κ D hP)) :
    P.IsArithmeticBallUniformized X N := by
  have : IsIntegral X.toOver.left := X.property
  have : Smooth X.toOver.hom := X.presentation.smooth
  have : Mono f := Over.mono_of_mono_left f
  obtain ⟨e, he⟩ := Principal.ProjectiveComponent.exists_homeomorph_of_equal_embedding_ranges
    (M.realBallOrbitMap hM κ D hP hκ hN) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
    (M.realBallOrbitMap_isOpenEmbedding hM κ D hP hκ hN).isEmbedding
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion f).isEmbedding
    ((M.realBallOrbitMap_range hM κ D hP hκ hN).trans hrange.symm)
  let q : P.Domain → X.analyticSpace := e ∘ q₀
  have hq (z : P.Domain) : q z ≫ f = M.realBallPoint hM κ D hP z := he (q₀ z)
  have hsurj : Function.Surjective q := e.surjective.comp
    (Hermitian.BallQuotient.HermitianBall.orbitProjection_surjective P H D.normalizer D.hermitian
      P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1
      (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1 Λ N)
  have hH := Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix_symmetry A.polarized A.action s hs rfl hdegree A.rosati
    P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1
  have hdet := Intrinsic.HermitianNondegenerate.IntrinsicHermitianMarking.markedHermitianMatrix_det_ne_zero A.polarized A.action s hs rfl hdegree A.rosati
    P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1
  have hΛ := Intrinsic.PELMarking.IntrinsicPELMarking.markedLattice_full_stable A.polarized.abelian
    (Polarized.Projectivity.polarizedNativeProjectivePresentation A.polarized) A.action s hs rfl hdegree
  have hdef := A.originalHermitianMatrix_compact hs hdegree hP hκ
  have hcover : IsCoveringMap q :=
    (Hermitian.BallQuotient.HermitianBall.orbitProjection_covering P H D.normalizer D.hermitian
      P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1
      (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1 Λ N hP hH hdet hΛ hdef hN).homeomorph_comp e
  have hderiv (z : P.Domain) := M.realBall_lift_derivative hM κ D hP hκ f hdim q hq z
  refine ⟨H, Λ, D.normalizer, hH, hdet, hΛ, han, D.hermitian, hdef, q,
    ⟨hsurj, hcover, fun z => (hderiv z).1, fun z => (hderiv z).2⟩, ?_⟩
  intro z w
  change e (q₀ z) = e (q₀ w) ↔ _
  exact e.injective.eq_iff.trans
    (Hermitian.BallQuotient.HermitianBall.orbitProjection_fibers P H D.normalizer D.hermitian
      P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1
      (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1 Λ N z w)

include D hP in
/-- The full ball through the original object is its actual projective
component, with the original arithmetic lattice in its covering fibers. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_realBall_projective_component
    (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation (M.complexFiber κ)) (hN : 3 ≤ N)
    (han : ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Datum.RankThreePELDatum.matrixHermitian H v v = 0 → v = 0) :
    ∃ X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety,
      M.IsProjectiveComponent κ (ConnectedComponents.mk (M.objectPoint hM κ A)) X ∧
        P.IsArithmeticBallUniformized X N := by
  have : LocallyOfFiniteType (M.complexFiber κ).hom := M.complexFiber_locallyFiniteType κ
  let Y := M.complexFiber κ
  let V := Set.range (M.realBallPoint hM κ D hP)
  have hcompact := M.realBallImage_compact hM κ D hP hκ hN han
  obtain ⟨hopen, hconnected, hsmooth⟩ := M.realBallImage_open_connected_smooth hM κ D hP hκ hN
  obtain ⟨R, hRo, hRc, ⟨Pj⟩, hrange⟩ :=
    QuasiProjectiveComponents.exists_projective_open_piece_of_compact_connected_analytic_open Q V hopen hcompact hconnected
      (fun _ hx => hsmooth hx)
  have : IsOpenImmersion R.inclusion := hRo
  have : IsClosedImmersion R.inclusion := hRc
  let X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨{
    carrier := R.carrier
    structureMap := R.inclusion ≫ Y.hom
    projective := Pj
    smooth := R.smooth }, R.integral⟩
  let f : X.toOver ⟶ Y := Over.homMk R.inclusion rfl
  have : IsOpenImmersion f.left := hRo
  have : IsClosedImmersion f.left := hRc
  have hfRange : Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) = V := hrange
  let x := M.objectPoint hM κ A
  have hx : x ∈ V := M.objectPoint_mem_realBallImage hM κ D hP hκ
  have hxR : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ R.support := by
    have hmem : x ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := hfRange.symm ▸ hx
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion f] at hmem
    exact hmem
  obtain ⟨S, hSo, hSdim, t, ht⟩ := M.exists_realBall_open_surface hM κ D hP hκ hN D.point
  have : IsOpenImmersion S.inclusion := hSo
  have htx : t ≫ Intrinsic.SmoothStrata.smoothPieceInclusion Y S = x :=
    ht.trans (M.realBallPoint_origin hM κ D hP hκ)
  have hxS : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ S.support := by
    rw [← htx]
    exact ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying t, rfl⟩
  have : Etale ((𝟙 Y : Y ⟶ Y).left) := inferInstanceAs (Etale (𝟙 Y.left))
  have hdim : X.complexDimension = 2 :=
    (Reference.PointTopology.openPiece_dimension_eq_of_etale_span (𝟙 Y) (𝟙 Y) R S
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x) hxR hxS).trans hSdim
  have hclopen : IsClopen V := by
    refine ⟨?_, hopen⟩
    rw [← hfRange]
    exact (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion f).isClosed_range
  have hcomponent := Principal.ProjectiveComponent.clopen_connected_eq_component_fiber V hclopen hconnected x hx
  refine ⟨X, ⟨hdim, f, hRo, hRc, hfRange.trans hcomponent⟩, ?_⟩
  exact M.arithmetic_uniformization_of_realBall_image hM κ D hP hκ hN han X f hdim hfRange

include hM hP in
/-- A second selected embedding supplies anisotropy for every original
object, so every analytic component is projective and arithmetic. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.hasProjectiveBallComponents_of_one_lt
    (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation (M.complexFiber κ))
    (hN : 3 ≤ N) (hs' : 1 < s) (hdeg : Module.finrank ℚ E = 2 * s) :
    M.HasProjectiveBallComponents κ := by
  intro C
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  let B := M.universal.pullback (M.complexPointBaseEquiv κ x)
  have hpos : 0 < s := lt_trans Nat.zero_lt_one hs'
  let D₀ := Intrinsic.BallCoordinateData.nativeBallCoordinateData B hpos hdeg hP hκ
  obtain ⟨X, hX, hu⟩ := M.exists_realBall_projective_component hM κ D₀ hP hκ Q hN
    (B.originalHermitianMatrix_anisotropic hpos hdeg hP hκ hs')
  refine ⟨X, ?_, hu⟩
  simpa only [B, M.objectPoint_universal hM κ] using hX

end FinePELModel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Real.BallProjectiveComponents
