import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Cover
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AnalyticRestriction

/-! # Open Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.OpenChart.BundleCycles

noncomputable section

section

/-! Coordinates on an actual affine open source lift to the retained finite support cover and preserve the full ambient square and compact bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

variable {S Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (g : S ⟶ Y) [IsFinite g.left]
  (Z : IrreducibleCloseds S.left)

local notation "ML" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Cover.BundleCycles.finiteSupportSourceOver g Z))) → ℂ

omit [AlgebraicGeometry.IsIntegral S.left] [AlgebraicGeometry.IsIntegral Y.left] in
theorem finiteSupportCover_ambient_square : FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap g Z ≫ g =
    FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap g Z ≫ FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap g Z :=
  FiniteSupport.Cover.BundleCycles.finiteSupportRegularCover_ambient_square g Z

omit [AlgebraicGeometry.IsIntegral S.left] [AlgebraicGeometry.IsIntegral Y.left] in
theorem finiteSupportCover_liftBase_eq : CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.liftBase (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap g Z) g =
    CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap g Z) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) := by
  funext x
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap g Z) g x).symm.trans
    ((congrArg (fun f => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) (finiteSupportCover_ambient_square g Z)).trans
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap g Z) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) x))

variable (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))

abbrev finiteSupportLocalSource := CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap g Z) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap g Z))
  (CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase_analytic (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap g Z) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap g Z)) U

def finiteSupportCoverToLiftSource : finiteSupportLocalSource g Z U → CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.liftSource (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap g Z) g U :=
  fun x => ⟨x.val, (congrArg (fun t : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y => t ∈ U)
    (congrFun (finiteSupportCover_liftBase_eq g Z) x.val)).mpr x.property⟩

theorem finiteSupportCoverToLiftSource_analytic : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, ML) ω (finiteSupportCoverToLiftSource g Z U) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.liftSource (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap g Z) g U)
    (finiteSupportCoverToLiftSource g Z U) ω).mp
  exact (show ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, ML) ω
    (Subtype.val : finiteSupportLocalSource g Z U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (FiniteSupport.Cover.BundleCycles.finiteSupportSourceOver g Z)) from contMDiff_subtype_val)

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ S) [IsOpenImmersion a.left]
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

def finiteSupportAffineLift : finiteSupportLocalSource g Z U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X :=
  CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.sourceLift a (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap g Z) g U hcover ∘ finiteSupportCoverToLiftSource g Z U

theorem finiteSupportAffineLift_analytic : ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, MX) ω (finiteSupportAffineLift g Z U a hcover) :=
  (CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.sourceLift_analytic a (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap g Z) g U hcover).comp
    (finiteSupportCoverToLiftSource_analytic g Z U)

theorem finiteSupportAffineLift_commutes (x : finiteSupportLocalSource g Z U) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a (finiteSupportAffineLift g Z U a hcover x) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap g Z) x.val :=
  CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.sourceLift_commutes a (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap g Z) g U hcover (finiteSupportCoverToLiftSource g Z U x)

variable [IsAffine X.left] {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

def finiteSupportAffineCoordinates : finiteSupportLocalSource g Z U → Fin d → ℂ :=
  CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f ∘ finiteSupportAffineLift g Z U a hcover

theorem finiteSupportAffineCoordinates_analytic :
    ContMDiff 𝓘(ℂ, ML) 𝓘(ℂ, Fin d → ℂ) ω (finiteSupportAffineCoordinates g Z U a hcover f) :=
  (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f).comp (finiteSupportAffineLift_analytic g Z U a hcover)

theorem finiteSupportAffineCoordinates_bound (K : Set (Fin d → ℂ))
    (hb : ∀ y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U →
      CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y ∈ K) (x : finiteSupportLocalSource g Z U) :
    finiteSupportAffineCoordinates g Z U a hcover f x ∈ K :=
  CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions.SchemeLift.sourceLift_bound a (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap g Z) g U hcover
    (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) K hb (finiteSupportCoverToLiftSource g Z U x)

end

/-! Restricting an actual finite map to an affine base open constructs the affine source, the ambient commuting square, and the full analytic fiber cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} (k : S ⟶ N) [IsFinite k.left] (B : N.left.Opens)

abbrev finiteAffineBase : Over Foundations.Scheme.ProjectiveSpace.complexBase := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver N B
abbrev finiteAffineSource : Over Foundations.Scheme.ProjectiveSpace.complexBase := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver S (k.left ⁻¹ᵁ B)

def finiteAffineMap : finiteAffineSource k B ⟶ finiteAffineBase B := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap k B

def finiteAffineSourceInclusion : finiteAffineSource k B ⟶ S := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion S (k.left ⁻¹ᵁ B)

def finiteAffineBaseInclusion : finiteAffineBase B ⟶ N := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion N B

instance finiteAffineMap_finite : IsFinite (finiteAffineMap k B).left :=
  inferInstanceAs (IsFinite (k.left ∣_ B))

instance finiteAffineSourceInclusion_open : IsOpenImmersion (finiteAffineSourceInclusion k B).left :=
  inferInstanceAs (IsOpenImmersion (k.left ⁻¹ᵁ B).ι)

instance finiteAffineBaseInclusion_open : IsOpenImmersion (finiteAffineBaseInclusion B).left :=
  inferInstanceAs (IsOpenImmersion B.ι)

omit [IsFinite (Over.Hom.left k)] in
theorem finiteAffineChart_square : finiteAffineSourceInclusion k B ≫ k =
    finiteAffineMap k B ≫ finiteAffineBaseInclusion B :=
  (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap_inclusion k B).symm

instance finiteAffineBase_smooth [Smooth N.hom] : Smooth (finiteAffineBase B).hom :=
  inferInstanceAs (Smooth (B.ι ≫ N.hom))

instance finiteAffineSource_smooth [Smooth S.hom] : Smooth (finiteAffineSource k B).hom :=
  inferInstanceAs (Smooth ((k.left ⁻¹ᵁ B).ι ≫ S.hom))

instance finiteAffineBase_integral [IsIntegral N.left] [Nonempty B] : IsIntegral (finiteAffineBase B).left :=
  inferInstanceAs (IsIntegral (B : Scheme))

instance finiteAffineSource_integral [IsIntegral S.left] [Nonempty (k.left ⁻¹ᵁ B)] :
    IsIntegral (finiteAffineSource k B).left :=
  inferInstanceAs (IsIntegral ((k.left ⁻¹ᵁ B) : Scheme))

theorem finiteAffineSource_affine (hB : IsAffineOpen B) : IsAffine (finiteAffineSource k B).left := by
  let : IsAffine (finiteAffineBase B).left := hB
  exact isAffine_of_isAffineHom (finiteAffineMap k B).left

omit [IsFinite (Over.Hom.left k)] in
theorem finiteAffineSourceInclusion_analytic_range : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (finiteAffineSourceInclusion k B)) =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k ⁻¹' (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen N B : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) := by
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion]
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S → S.left) ⁻¹'
    Set.range (k.left ⁻¹ᵁ B).ι = _
  rw [Scheme.Opens.range_ι]
  rfl

theorem finiteAffineBaseInclusion_analytic_range : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (finiteAffineBaseInclusion B)) =
    (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen N B : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) := by
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion]
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N → N.left) ⁻¹' Set.range B.ι = _
  rw [Scheme.Opens.range_ι]
  rfl

omit [IsFinite (Over.Hom.left k)] in
theorem finiteAffineChart_covers_fibers (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
    (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (finiteAffineBaseInclusion B))) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (finiteAffineSourceInclusion k B)) := by
  rw [finiteAffineSourceInclusion_analytic_range]
  intro x hx
  exact (Set.ext_iff.mp (finiteAffineBaseInclusion_analytic_range B) _).mp (hU hx)

instance finiteAffineSource_metrizable [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)] :
    MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (finiteAffineSource k B)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (finiteAffineSourceInclusion k B)).isEmbedding.metrizableSpace

instance finiteAffineBase_metrizable [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] :
    MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (finiteAffineBase B)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (finiteAffineBaseInclusion B)).isEmbedding.metrizableSpace

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.OpenChart.BundleCycles
