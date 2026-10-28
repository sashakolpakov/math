import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELTangentDimension
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FinePELSurfaceStratum
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.Chart
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.QuotientCriterion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDifferentials
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.OverScalars
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothRetract
import Mathlib.AlgebraicGeometry.SpreadingOut
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion

/-! # PEL Stratum Local Regularity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PELStratumLocalRegularity

noncomputable section

/-! The actual fine PEL space is smooth at every complex point lying
on a smooth two-dimensional immersed subspace. The map of stalks is a
surjection onto a smooth local algebra, while the original tangent bound
forces that quotient to be an isomorphism. This controls nilpotents in
the ambient space and supplies a smooth reference point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

theorem schemeStalkScalar_fromSpecStalk (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (x : X.left) :
    letI := IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra.scalarAlgebra X.hom x
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (X.left.presheaf.stalk x))) =
      X.left.fromSpecStalk x ≫ X.hom := by
  let := IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra.scalarAlgebra X.hom x
  let U := (X.left.affineCover.f (X.left.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.left.affineCover.f _)
  have hx : x ∈ U := X.left.affineCover.covers x
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
  have hscalar : CommRingCat.ofHom (algebraMap ℂ (X.left.presheaf.stalk x)) =
      CommRingCat.ofHom (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap X.hom U) ≫ X.left.presheaf.germ U x hx := by
    ext c
    exact ((IntersectionTheory.ProjectionFormula.Stalk.ScalarMaps.germ X.hom U x hx).commutes c).symm
  rw [hscalar, Spec.map_comp, Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec X.hom U hU, ← Category.assoc]
  change hU.fromSpecStalk hx ≫ X.hom = _
  rw [hU.fromSpecStalk_eq_fromSpecStalk hx]

theorem schemeStalkScalar_essFiniteType (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] (x : X.left) :
    letI := IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra.scalarAlgebra X.hom x
    Algebra.EssFiniteType ℂ (X.left.presheaf.stalk x) := by
  let := IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra.scalarAlgebra X.hom x
  let U := (X.left.affineCover.f (X.left.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.left.affineCover.f _)
  have hx : x ∈ U := X.left.affineCover.covers x
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
  let : Algebra.FiniteType ℂ Γ(X.left, U) :=
    (RingHom.finiteType_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of ℂ)).inv (X.hom.appLE ⊤ U le_top)).mpr
        (X.hom.finiteType_appLE (isAffineOpen_top _) hU le_top)
  let := TopCat.Presheaf.algebra_section_stalk X.left.presheaf (⟨x, hx⟩ : U)
  let : IsScalarTower ℂ Γ(X.left, U) (X.left.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq (fun c => ((IntersectionTheory.ProjectionFormula.Stalk.ScalarMaps.germ X.hom U x hx).commutes c).symm)
  let T := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : IsLocalization T (X.left.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hx⟩
  let : Algebra.EssFiniteType Γ(X.left, U) (X.left.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization _ T
  exact Algebra.EssFiniteType.comp ℂ Γ(X.left, U) (X.left.presheaf.stalk x)

theorem schemeStalkScalar_formallySmooth_iff (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFinitePresentation X.hom] (x : X.left) :
    letI := IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra.scalarAlgebra X.hom x
    Algebra.FormallySmooth ℂ (X.left.presheaf.stalk x) ↔ x ∈ X.hom.smoothLocus := by
  let := IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra.scalarAlgebra X.hom x
  let b := CycleClass.Thom.StalkRetractionScalars.Constructions.stalkBaseMap X.hom x
  have h := RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (.of ℂ)).inv b
  exact h.trans (CycleClass.Thom.Scheme.SmoothRetract.Constructions.stalkBaseMap_formallySmooth_iff X.hom x)

/-- An isomorphism on the actual stalks of an immersion spreads to an
open neighborhood with an inverse over the original ambient scheme. -/
theorem exists_open_section_of_stalkMap_bijective
    {X Y : Scheme} (f : X ⟶ Y) [IsImmersion f] [IsLocallyNoetherian Y]
    (x : X) (hb : Function.Bijective (f.stalkMap x).hom) :
    ∃ (U : Y.Opens) (hx : f x ∈ U) (g : U.toScheme ⟶ X),
      IsOpenImmersion g ∧ g ≫ f = U.ι ∧ g ⟨f x, hx⟩ = x := by
  let : IsIso (f.stalkMap x) := (ConcreteCategory.isIso_iff_bijective _).mpr hb
  let φ := Spec.map (inv (f.stalkMap x)) ≫ X.fromSpecStalk x
  have hφ : φ ≫ f = Y.fromSpecStalk (f x) ≫ 𝟙 Y := by
    dsimp only [φ]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk f,
      ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp, Category.comp_id]
  obtain ⟨U, hx, g, _, hg⟩ := spread_out_of_isGermInjective' (𝟙 Y) f φ hφ
  have hgf : g ≫ f = U.ι := by simpa only [Category.comp_id] using hg
  have hpb : IsPullback g (𝟙 _) f U.ι :=
    IsPullback.of_vert_isIso_mono ⟨by simpa only [Category.id_comp] using hgf⟩
  refine ⟨U, hx, g, MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    hpb.flip inferInstance, hgf, ?_⟩
  apply f.isEmbedding.injective
  change (g ≫ f) ⟨f x, hx⟩ = f x
  rw [hgf]
  rfl

/-- Isomorphisms on the stalks at genuine complex points make an
immersion open for the native complex-point topology. -/
theorem isOpenMap_complexPoints_of_stalkMap_bijective
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsImmersion f.left]
    [IsLocallyNoetherian Y.left]
    (hb : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X,
      Function.Bijective (f.left.stalkMap (x.left (IsLocalRing.closedPoint ℂ))).hom) :
    IsOpenMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  intro V hV
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨U, hu, g, hg, hgf, hgx⟩ :=
    exists_open_section_of_stalkMap_bijective f.left
      (x.left (IsLocalRing.closedPoint ℂ)) (hb x)
  let := hg
  let T : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (U.ι ≫ Y.hom)
  let j : T ⟶ Y := Over.homMk U.ι
  let k : T ⟶ X := Over.homMk g (by
    rw [← f.w, ← Category.assoc, hgf]
    rfl)
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
  let : IsOpenImmersion k.left := hg
  have hkf : k ≫ f = j := by
    apply Over.OverMorphism.ext
    exact hgf
  have hxk : x ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k) := by
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion k]
    change x.left ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint ∈ Set.range g
    rw [Subsingleton.elim ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint (IsLocalRing.closedPoint ℂ)]
    exact ⟨⟨_, hu⟩, hgx⟩
  obtain ⟨u, hu⟩ := hxk
  have huV : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k u ∈ V := hu.symm ▸ hx
  have huj : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j u = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x := by
    rw [← hkf, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, hu]
  have hW := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenMap_map_of_isOpenImmersion j _
    (hV.preimage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map k))
  refine Filter.mem_of_superset (hW.mem_nhds ⟨u, huV, huj⟩) ?_
  rintro z ⟨v, hv, rfl⟩
  refine ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k v, hv, ?_⟩
  rw [← ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, hkf]

namespace FinePELModel

attribute [local implicit_reducible] Models.FinePELModel.complexFiber

variable {E K : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] [IsGalois ℚ E] [Field K]
    {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hP : P.IsAdmissible) (hM : M.IsFine)
    (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    [LocallyOfFiniteType M.space.hom]

local instance : LocallyOfFinitePresentation (M.complexFiber κ).hom :=
  inferInstanceAs (LocallyOfFinitePresentation
    (Limits.pullback.snd M.space.hom (Spec.map (CommRingCat.ofHom κ))))

include hP hM hκ in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.complexPoint_surface_stalk_data
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ M.complexFiber κ) [IsImmersion f.left]
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2) :
    Function.Bijective (f.left.stalkMap (x.left (IsLocalRing.closedPoint ℂ))).hom ∧
      (x ≫ f).left (IsLocalRing.closedPoint ℂ) ∈ (M.complexFiber κ).hom.smoothLocus := by
  let X := M.complexFiber κ
  let b := x.left (IsLocalRing.closedPoint ℂ)
  let a := f.left b
  let A : Type := X.left.presheaf.stalk a
  let B : Type := S.left.presheaf.stalk b
  let : Algebra ℂ A := IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra.scalarAlgebra X.hom a
  let : Algebra ℂ B := IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra.scalarAlgebra S.hom b
  let εA : A →ₐ[ℂ] ℂ := IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra.evaluation X.hom (x ≫ f).left (x ≫ f).w
  let εB : B →ₐ[ℂ] ℂ := IntersectionTheory.ProjectionFormula.Stalk.PointAlgebra.evaluation S.hom x.left x.w
  let : Algebra A ℂ := εA.toRingHom.toAlgebra
  let : Algebra B ℂ := εB.toRingHom.toAlgebra
  let : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq (fun c => (εA.commutes c).symm)
  let : IsScalarTower ℂ B ℂ := IsScalarTower.of_algebraMap_eq (fun c => (εB.commutes c).symm)
  let φ : A →ₐ[ℂ] B := IntersectionTheory.ProjectionFormula.Stalk.OverScalars.map f.left S.hom X.hom f.w b
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  let : IsScalarTower A B ℂ := IsScalarTower.of_algebraMap_eq' (by
    exact congrArg CommRingCat.Hom.hom (Scheme.stalkClosedPointTo_comp x.left f.left))
  have : LocallyOfFiniteType X.hom := M.complexFiber_locallyFiniteType κ
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : IsNoetherianRing A := inferInstance
  have : Algebra.EssFiniteType ℂ A := schemeStalkScalar_essFiniteType X a
  have : Algebra.EssFiniteType ℂ B := schemeStalkScalar_essFiniteType S b
  have : SmoothOfRelativeDimension 2 S.hom := by
    rw [← hdim]
    exact Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension S.hom
  obtain ⟨hBS, hBFree, hBFinite, hBdim⟩ := IntersectionTheory.ProjectionFormula.Smooth.StalkDifferentials.data S.hom 2 b
  let := hBS
  let := hBFree
  let := hBFinite
  let j : EtaleSplittingAt.EtaleSplitting.affineOver ℂ A ⟶ X :=
    Over.homMk (X.left.fromSpecStalk a) (schemeStalkScalar_fromSpecStalk X a).symm
  let : Mono j := Over.mono_of_mono_left j
  have hAdim : Module.finrank ℂ (Derivation ℂ A ℂ) ≤ 2 :=
    AbelianScheme.IsogenyQuotient.FinePELTangentDimension.Construction.FinePELModel.affineTangent_finrank_le_two M hP hM κ hκ A j
  have hBderiv : Module.finrank ℂ (Derivation ℂ B ℂ) = 2 := by
    rw [← ReferenceFamily.Smooth.QuotientCriterion.coefficientDifferential_finrank_eq_derivations ℂ B ℂ, Module.finrank_baseChange, hBdim]
  have hbij : Function.Bijective (algebraMap A B) :=
    ReferenceFamily.Smooth.QuotientCriterion.augmentedSmoothQuotient_algebraMap_bijective ℂ A B
      (f.left.stalkMap_surjective b) (hAdim.trans_eq hBderiv.symm)
  let e : A ≃ₐ[ℂ] B := AlgEquiv.ofBijective φ hbij
  have hA : Algebra.FormallySmooth ℂ A := Algebra.FormallySmooth.of_equiv e.symm
  exact ⟨hbij, (schemeStalkScalar_formallySmooth_iff X a).mp hA⟩

include hP hM hκ in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.complexPoint_mem_smoothLocus_of_surface
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ M.complexFiber κ) [IsImmersion f.left]
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2) :
    (x ≫ f).left (IsLocalRing.closedPoint ℂ) ∈ (M.complexFiber κ).hom.smoothLocus :=
  (M.complexPoint_surface_stalk_data hP hM κ hκ f x hdim).2

include hP hM hκ in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.complexPoints_isOpenMap_of_surface
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ M.complexFiber κ) [IsImmersion f.left]
    (hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom = 2) :
    IsOpenMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  have : LocallyOfFiniteType (M.complexFiber κ).hom := M.complexFiber_locallyFiniteType κ
  have : IsLocallyNoetherian (M.complexFiber κ).left :=
    LocallyOfFiniteType.isLocallyNoetherian (M.complexFiber κ).hom
  exact isOpenMap_complexPoints_of_stalkMap_bijective f
    (fun x => (M.complexPoint_surface_stalk_data hP hM κ hκ f x hdim).1)

include hM hκ in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_reference_smooth_point [QuasiCompact M.space.hom]
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ a : P.domain,
      (M.referencePoint hM κ hP hκ a).left (IsLocalRing.closedPoint ℂ) ∈
        (M.complexFiber κ).hom.smoothLocus := by
  obtain ⟨R, hR, a, x, hx⟩ :=
    M.exists_reference_smooth_surface_stratum hM κ hP hκ hs hdegree
  refine ⟨a, ?_⟩
  have hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension R.toOver.hom = 2 :=
    (Intrinsic.SmoothStrata.smoothPiece_dimension (M.complexFiber κ) R).trans hR
  have h := M.complexPoint_mem_smoothLocus_of_surface hP hM κ hκ
    (Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R) x hdim
  simpa only [hx] using h

include hM hκ in
/-- The original reference locus contains an actual nonempty analytic
open subset of the original fine model. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.exists_open_reference_neighborhood [QuasiCompact M.space.hom]
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ (a : P.domain) (V : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.complexFiber κ))),
      IsOpen V ∧ M.referencePoint hM κ hP hκ a ∈ V ∧
        V ⊆ Set.range (M.referencePoint hM κ hP hκ) := by
  obtain ⟨R, hR, a, x, hx⟩ :=
    M.exists_reference_smooth_surface_stratum hM κ hP hκ hs hdegree
  let f := Intrinsic.SmoothStrata.smoothPieceInclusion (M.complexFiber κ) R
  have hdim : Betti.AffineDimension.Realization.functionFieldDifferentialDimension R.toOver.hom = 2 :=
    (Intrinsic.SmoothStrata.smoothPiece_dimension (M.complexFiber κ) R).trans hR
  obtain ⟨e, he, _, _, _, hmod⟩ :=
    M.exists_native_reference_moduli_chart hM κ hP hκ f hs hdegree hdim x a hx
  refine ⟨a, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f '' e.source,
    M.complexPoints_isOpenMap_of_surface hP hM κ hκ f hdim _ e.open_source,
    ⟨x, he, hx⟩, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨hp, hpoint⟩ := hmod z hz
  exact ⟨⟨e z, hp⟩, hpoint.symm⟩

end FinePELModel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PELStratumLocalRegularity
