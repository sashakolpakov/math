import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SummandTransport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntrinsicHecke

/-! # Comparison Intrinsic Class -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass
section

/-! Construct projectors for the genuine native theta classes, with their
characters in the fixed algebraic closure and their ranges identified with
GeometricComparison's actual complex Betti summands, including all coefficient conjugates. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM
open scoped Classical TensorProduct

theorem native_theta_comparison_projectors
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput)
    (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ]
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) :
    letI := Intrinsic.Comparison.nativeActiveCommRing D e hElementaryDivisors
    ∃ R : (Intrinsic.Comparison.nativeComparisonModel D hg hq j).HeckeRealization (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q),
      (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHecke D.pel.complexEmbedding R =
        (fun h => (Intrinsic.Forms.activeBettiAction D A e h : Module.End ℚ D.pel.H1)) ∧
      ∃ L : IntermediateField ℚ ℂ, NumberField L ∧ IsGalois ℚ L ∧ E ≤ L ∧
        ∃ (hLalg : L ≤ HeckeCycles.Coefficients.CM.algebraicField) (n : ℕ)
          (p : Fin n → L ⊗[ℚ] (D.pel.H1 →ₗ[ℚ] D.pel.H1))
          (χ : Fin n → RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[ℚ] AlgebraicClosure ℚ),
          let P := fun i => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L D.pel.H1 D.pel.H1 (p i)
          let B := fun i => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange L D.pel.H1 D.pel.H1 (p i))
          let H := Intrinsic.Base.nativeH1 D hHodgeDecomposition hg
          let c := ComparisonBetti.Intrinsic.nativeBettiComplexification D hg
          (∀ i, (P i).comp (P i) = P i) ∧
          (∀ i, LinearMap.range (P i) = Definitions.CM.conjugateSpace L (B i) 1) ∧
          (∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H) ∧
          (∀ i, ∃ φ, P i (Intrinsic.ThetaClass.nativeThetaClass D hg Θ φ) ≠ 0) ∧
          (∀ φ, ∑ i, P i (Intrinsic.ThetaClass.nativeThetaClass D hg Θ φ) = Intrinsic.ThetaClass.nativeThetaClass D hg Θ φ) ∧
          (∀ i, LinearMap.range (c.conj (P i)) =
            (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHeckeSummand D.pel.complexEmbedding R
              (fun h => j.complexClosure (χ i h))) ∧
          (∀ i (σ : Gal(L/ℚ)),
            let Pσ := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients L D.pel.H1 D.pel.H1
              (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ L (D.pel.H1 →ₗ[ℚ] D.pel.H1) σ (p i))
            ∃ τ : Gal(AlgebraicClosure ℚ/ℚ),
              (∀ a : L, j.complexClosure (τ ((HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j.complexClosure).symm
                (IntermediateField.inclusion hLalg a))) = (σ a : ℂ)) ∧
              Pσ ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H ∧
              LinearMap.range (c.conj Pσ) =
                (Intrinsic.Comparison.nativeComparisonModel D hg hq j).bettiHeckeSummand D.pel.complexEmbedding R
                  (fun h => j.complexClosure (τ (χ i h)))) := by
  let := Intrinsic.Comparison.nativeActiveCommRing D e hElementaryDivisors
  obtain ⟨R, _, hR⟩ := Intrinsic.Comparison.native_active_comparison_realization D hg hq hIsogenyQuotient A hA e hElementaryDivisors j
  obtain ⟨L, hL, hGal, hEL, hLalg, n, p, χ, hid, hr, hh, hocc, hsum, hχ, hconj⟩ :=
    HeckeCycles.ComparisonProjectors.CM.construct_comparison_projectors E (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg)
      (Intrinsic.Forms.activeBettiAction D A e)
      (IntrinsicHecke.Intrinsic.native_active_hecke_isHodgeMap D hHodgeDecomposition hConstruction hHodgeComparison hg hq hIsogenyQuotient A hA e)
      (Intrinsic.ThetaClass.nativeThetaClass D hg Θ) j.complexClosure
  refine ⟨R, hR, L, hL, hGal, hEL, hLalg, n, p, χ, hid, hr, hh, hocc, hsum, ?_, ?_⟩
  · intro i
    rw [SummandTransport.Comparison.conjugate_range, hχ i]
    exact SummandTransport.Intrinsic.native_comparison_summand D hg hq A e hElementaryDivisors j R hR _
  · intro i σ
    obtain ⟨τ, hτ, hH, hspace⟩ := hconj i σ
    refine ⟨τ, hτ, hH, ?_⟩
    rw [SummandTransport.Comparison.conjugate_range, hspace]
    exact SummandTransport.Intrinsic.native_comparison_summand D hg hq A e hElementaryDivisors j R hR _

end

/-! Whenever the actual native Albanese is given a projective embedding,
its geometric filtration agrees with the native Hodge structure already
constructed through IntegralModel. The agreement is proved from actual pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM
open scoped TensorProduct

section

theorem holomorphic_eq_of_identity_hodge
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    (H K : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (h : ComplexMultiplication.WeightOne.CM.IsHodgeMap H K LinearMap.id) :
    H.holomorphic = K.holomorphic := by
  have hh : H.holomorphic ≤ K.holomorphic := by
    intro x hx
    simpa only [LinearMap.baseChange_id, LinearMap.id_apply] using h x hx
  have ha : H.antiholomorphic ≤ K.antiholomorphic := by
    intro x hx
    simpa only [LinearMap.baseChange_id, LinearMap.id_apply] using h.map_antiholomorphic hx
  exact (le_iff_eq_of_codisjoint_of_disjoint H.complementary.codisjoint
    (K.complementary.disjoint.mono_right ha).symm).mp hh

end

namespace Intrinsic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def nativeAlbanesePresentation (hg : D.pel.HasIntegralModelGeometry)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom) :
    Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := D.pel.complexAlbanese.X.left
  structureMap := D.pel.complexAlbanese.X.hom
  projective := P
  smooth := by
    change Smooth (((HeckeCycles.AlbaneseModel.CM.arithmeticAlbanese D.pel hg).2.pullback D.pel.generic).pullback
      D.pel.complexGenericPoint).scheme.hom
    infer_instance

theorem native_holomorphic_eq_projective
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hg : D.pel.HasIntegralModelGeometry)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom) :
    (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg).holomorphic =
      (Mem.canonicalH1 hHodgeDecomposition (nativeAlbanesePresentation D hg P)).holomorphic := by
  have h := Intrinsic.ProjectivePullback.native_projective_pullback_isHodgeMap D hHodgeDecomposition hg
    (nativeAlbanesePresentation D hg P) (𝟙 D.pel.complexAlbanese.X)
  have he : PELModuli.IntegralModel.Product.bettiPullbackQ (𝟙 D.pel.complexAlbanese.X) 1 =
      LinearMap.id := by
    exact congrArg ModuleCat.Hom.hom
      ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) 1).map_id (Opposite.op D.pel.complexAlbanese.X))
  have hi : ComplexMultiplication.WeightOne.CM.IsHodgeMap (Mem.canonicalH1 hHodgeDecomposition (nativeAlbanesePresentation D hg P))
      (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) LinearMap.id := he ▸ h
  exact (holomorphic_eq_of_identity_hodge _ _ hi).symm

theorem native_holomorphic_complex_image
    (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hg : D.pel.HasIntegralModelGeometry)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom) :
    (Intrinsic.Base.nativeH1 D hHodgeDecomposition hg).holomorphic.map (ComparisonBetti.Intrinsic.nativeBettiComplexification D hg).toLinearMap =
      (nativeAlbanesePresentation D hg P).pureBettiSubspace 1 0 := by
  rw [native_holomorphic_eq_projective D hHodgeDecomposition hg P]
  change (((nativeAlbanesePresentation D hg P).pureBettiSubspace 1 0).comap
      (ComparisonBetti.Intrinsic.nativeBettiComplexification D hg).toLinearMap).map
        (ComparisonBetti.Intrinsic.nativeBettiComplexification D hg).toLinearMap = _
  exact Submodule.map_comap_eq_of_surjective (ComparisonBetti.Intrinsic.nativeBettiComplexification D hg).surjective _

end Intrinsic

end AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass.Intrinsic
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open scoped _root_.CategoryTheory.Obj
section

/-! Identify the integration-defined native class with the class on an
actual projective presentation of the same Albanese, then prove pullback
naturality for every algebraic endomorphism. -/

open scoped TensorProduct

theorem presentationKaehlerComplexifiedClass_pullback (P Q : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (f : P.toOver ⟶ Q.toOver) (form : AbelianScheme.TateComparison.FormConstants.OneForms Q.toOver) :
    KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass P (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      (PELModuli.IntegralModel.Product.bettiPullbackQ f 1).baseChange ℂ (KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass Q form) := by
  apply (Mem.bettiComplexification P 1).injective
  change (Mem.bettiComplexification P 1)
    ((Mem.bettiComplexification P 1).symm
      (KaehlerClasses.Intrinsic.presentationKaehlerBettiClass P (AbelianScheme.TateComparison.FormConstants.formsPullback f form))) = _
  rw [LinearEquiv.apply_symm_apply]
  have h := Naturality.complexification_pullback f 1 (KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass Q form)
  change _ = Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f
    ((Mem.bettiComplexification Q 1)
      ((Mem.bettiComplexification Q 1).symm (KaehlerClasses.Intrinsic.presentationKaehlerBettiClass Q form))) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact (KaehlerClasses.Intrinsic.presentationKaehlerBettiClass_pullback P Q f form).trans h.symm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom)

theorem nativeKaehlerClass_eq_projective (form : D.pel.OneFormsA) :
    Intrinsic.ThetaClass.nativeKaehlerClass D hg form =
      KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass (nativeAlbanesePresentation D hg P) form := by
  apply ((Intrinsic.Base.nativeAlbaneseBettiEquiv D hg).baseChange ℚ ℂ _ _).injective
  change (Intrinsic.Base.nativeAlbaneseBettiEquiv D hg).toLinearMap.baseChange ℂ (Intrinsic.ThetaClass.nativeKaehlerClass D hg form) = _
  rw [Intrinsic.ThetaClass.nativeKaehlerClass_albanese]
  change _ = (Intrinsic.Base.nativeAlbaneseBettiEquiv D hg).toLinearMap.baseChange ℂ
    (KaehlerClasses.Intrinsic.presentationKaehlerComplexifiedClass (nativeAlbanesePresentation D hg P) form)
  rw [Intrinsic.Base.nativeAlbaneseBettiEquiv_eq_pullback]
  exact presentationKaehlerComplexifiedClass_pullback (Intrinsic.Base.singleBaseSpacePresentation D hg)
    (nativeAlbanesePresentation D hg P)
    ((Intrinsic.Base.singleBaseSpaceIso D hg).hom ≫ D.pel.complexAlbaneseMap hg) form

include P in
theorem nativeKaehlerClass_pullback (f : D.pel.complexAlbanese.X ⟶ D.pel.complexAlbanese.X)
    (form : D.pel.OneFormsA) :
    Intrinsic.ThetaClass.nativeKaehlerClass D hg (AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      (PELModuli.IntegralModel.Product.bettiPullbackQ f 1).baseChange ℂ (Intrinsic.ThetaClass.nativeKaehlerClass D hg form) := by
  rw [nativeKaehlerClass_eq_projective D hg P, nativeKaehlerClass_eq_projective D hg P]
  exact presentationKaehlerComplexifiedClass_pullback (nativeAlbanesePresentation D hg P)
    (nativeAlbanesePresentation D hg P) f form

include P in
theorem nativeKaehlerClass_integral (a : D.pel.EndK) (form : D.pel.OneFormsA) :
    Intrinsic.ThetaClass.nativeKaehlerClass D hg (D.pel.pullbackForms a form) =
      (D.pel.pullbackH1Integral a).baseChange ℂ (Intrinsic.ThetaClass.nativeKaehlerClass D hg form) :=
  nativeKaehlerClass_pullback D hg P
    ((Over.pullback D.pel.complexGenericPoint).map (AbelianScheme.TateComparison.End.endSchemeMap D.pel.albaneseGroup.X a)) form

end

/-! The actual integration-defined native class intertwines rational and
complex Hecke actions. Both rational pullbacks use the same denominator. -/

open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom)

include P

theorem nativeKaehlerClass_rational (a : D.pel.EndQ)
    (f : Module.End ℚ D.pel.H1) (g : Module.End ℂ D.pel.OneFormsA)
    (hf : D.pel.IsRationalH1Pullback a f) (hgf : D.IsRationalFormsPullback a g)
    (form : D.pel.OneFormsA) :
    Intrinsic.ThetaClass.nativeKaehlerClass D hg (g form) = f.baseChange ℂ (Intrinsic.ThetaClass.nativeKaehlerClass D hg form) := by
  obtain ⟨n, hn, b, hb⟩ := hf.1
  have hd := hf.2 n hn b hb
  have hdg := hgf.2 n hn b hb
  have h := nativeKaehlerClass_integral D hg P b form
  rw [← hd, ← hdg, LinearMap.smul_apply, map_smul,
    LinearMap.baseChange_smul, LinearMap.smul_apply] at h
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnsmul := h
  simp only [Nat.cast_smul_eq_nsmul] at hnsmul
  apply (smul_right_injective _ hnC)
  simpa only [Nat.cast_smul_eq_nsmul] using hnsmul

theorem nativeKaehlerClass_hecke
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (rho : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (hrho : ∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rho h))
    (t : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.FullHecke q s) (form : D.pel.OneFormsA) :
    Intrinsic.ThetaClass.nativeKaehlerClass D hg (rho t form) =
      (A.cohomologyAction t).baseChange ℂ (Intrinsic.ThetaClass.nativeKaehlerClass D hg form) :=
  nativeKaehlerClass_rational D hg P (A.algebraAction t) _ _ (hA.cohomology t) (hrho t) form

theorem nativeKaehlerClass_active
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (rho : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (hrho : ∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rho h))
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (t : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (form : D.pel.OneFormsA) :
    D.activeH1Complex A e t (Intrinsic.ThetaClass.nativeKaehlerClass D hg form) =
      Intrinsic.ThetaClass.nativeKaehlerClass D hg (D.activeFormsComplex rho e t form) := by
  apply RepresentationTheory.Theta.Geometric.Complexify.covariance_extends_to_complex (Intrinsic.ThetaClass.nativeKaehlerClass D hg)
  intro a α
  exact (nativeKaehlerClass_hecke D hg P hq hIsogenyQuotient A hA rho hrho
    (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e a) α).symm

theorem nativeThetaClass_hecke
    (hq : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
    (rho : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.FullHecke q s →ₗ[ℚ] Module.End ℂ D.pel.OneFormsA)
    (hrho : ∀ h, D.IsRationalFormsPullback (A.algebraAction h) (rho h))
    (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (hΘ : ∀ h φ, D.activeFormsComplex rho e h (Θ φ) = Θ (D.sphericalWeilComplex h φ))
    (t : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (φ : D.sphericalInputs) :
    D.activeH1Complex A e t (Intrinsic.ThetaClass.nativeThetaClass D hg Θ φ) =
      Intrinsic.ThetaClass.nativeThetaClass D hg Θ (D.sphericalWeilComplex t φ) := by
  change D.activeH1Complex A e t (Intrinsic.ThetaClass.nativeKaehlerClass D hg (Θ φ)) = _
  rw [nativeKaehlerClass_active D hg P hq hIsogenyQuotient A hA rho hrho e, hΘ]
  rfl

end AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass.Intrinsic

end

end OAI
