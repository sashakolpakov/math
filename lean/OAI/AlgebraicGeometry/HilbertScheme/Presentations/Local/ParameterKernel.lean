import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.FamilyCoordinateKernel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialEquivalence
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.StructureProperties
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.RingPointOpenLift

/-! # Parameter Kernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.ParameterKernel.GradedHilbert

noncomputable section

/-! Hilbert parameters over arbitrary local rings have Grassmannian
coordinates whose kernels are the canonical degree relations of their families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem exists_local_hilbert_parameter_coordinate_kernel
    (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    (f : Spec (.of R) ⟶ S)
    (x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) :
    ∃ Q : Module.Grassmannian R (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N → R) (Fintype.card ι),
      Q.toSubmodule = DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
          (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)))) N ∧
      Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f Q =
        x ≫ BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) := by
  let H := BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)
  let V := BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)
  let j := BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)
  let : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  let C := H.left.affineOpenCover
  obtain ⟨i, a, ha⟩ := RingPointOpenLift.localRingPoint_lift_openCover C.openCover x.left
  change C.I₀ at i
  change Spec (.of R) ⟶ Spec (C.X i) at a
  change a ≫ C.f i = x.left at ha
  let : IsOpenImmersion (C.f i) := C.map_prop i
  let A : Type u := C.X i
  have hA : IsNoetherianRing A := isLocallyNoetherian_Spec.mp
    (isLocallyNoetherian_of_isOpenImmersion (C.f i))
  let : IsNoetherianRing A := hA
  let g : Spec (.of A) ⟶ S := C.f i ≫ H.hom
  let z : Over.mk g ⟶ H := Over.homMk (C.f i) rfl
  have hw : a ≫ g = f := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ H.hom) ha).trans x.w)
  let b : Over.mk f ⟶ Over.mk g := Over.homMk a hw
  have hbx : b ≫ z = x := Over.OverMorphism.ext ha
  let φ : A →+* R := (Spec.preimage a).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = b.left := Spec.map_preimage a
  let F := Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) z V
  have hF : ∀ p : PrimeSpectrum A, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n g F))).toIdeal P :=
    (Noetherian.PolynomialEquivalence.GradedHilbert.boundedHilbertUniversalFamily_canonicalFiberPolynomial _ P hP z).affine_residue
  let D := Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineCoordinateGrassmannian g F P hF N hN ι hr
  let Q := Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ D
  refine ⟨Q, ?_, ?_⟩
  · have he := Noetherian.FamilyCoordinateKernel.GradedHilbert.noetherian_native_coordinate_baseChange_kernel g f b φ hφ F P hF hN hr
    rw [← Hilbert.Functor.pullbackFamily_comp, hbx] at he
    exact he
  · have hz : z ≫ j = Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint g D :=
      Noetherian.AffineParameterCoordinates.GradedHilbert.noetherianAffine_hilbert_parameter_coordinates g F P hF hN hr z rfl
    have hn := Affine.OverCoordinateBaseChange.Grassmannian.relativeQuotientClassifyingPoint_over_natural g f b φ hφ D
    change Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f Q = x ≫ j
    rw [← hn, ← hz, ← Category.assoc, hbx]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.ParameterKernel.GradedHilbert
