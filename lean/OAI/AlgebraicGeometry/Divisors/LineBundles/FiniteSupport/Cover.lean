import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportGoodOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.RestrictionDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicFiberDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicEtale

/-! # Cover -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Cover.BundleCycles

noncomputable section

section

/-! Genuine smooth finite-etale generic opens of the map induced on
an integral support by a finite morphism, with its exact residue degree. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] (Z : IrreducibleCloseds X.left)

local instance : IsIntegral (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z).left := inferInstanceAs (IsIntegral (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z))
local instance : IsIntegral (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)).left :=
  inferInstanceAs (IsIntegral (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)))

def finiteSupportGoodOpen : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)).Opens :=
  (CycleClass.Thom.Finite.SupportGoodOpen.Constructions.exists_smooth_etale_open f Z).choose

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportGoodOpen_spec :
    genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)) ∈ finiteSupportGoodOpen f Z ∧
      IsFinite (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap f Z ∣_ finiteSupportGoodOpen f Z) ∧
      Etale (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap f Z ∣_ finiteSupportGoodOpen f Z) ∧
      Smooth ((finiteSupportGoodOpen f Z).ι ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom) ∧
      Smooth ((CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap f Z ⁻¹ᵁ finiteSupportGoodOpen f Z).ι ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom) :=
  (CycleClass.Thom.Finite.SupportGoodOpen.Constructions.exists_smooth_etale_open f Z).choose_spec

def finiteSupportSourceOpen : (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).Opens := CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap f Z ⁻¹ᵁ finiteSupportGoodOpen f Z

instance finiteSupportGoodOpen_nonempty : Nonempty (finiteSupportGoodOpen f Z) :=
  ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)), (finiteSupportGoodOpen_spec f Z).1⟩⟩

instance finiteSupportSourceOpen_nonempty : Nonempty (finiteSupportSourceOpen f Z) :=
  ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z), by
    change CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap f Z (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)) ∈ finiteSupportGoodOpen f Z
    rw [CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap_genericPoint]
    exact (finiteSupportGoodOpen_spec f Z).1⟩⟩

def finiteSupportSourceOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z) (finiteSupportSourceOpen f Z)
def finiteSupportTargetOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)) (finiteSupportGoodOpen f Z)

instance finiteSupportSourceOver_integral : IsIntegral (finiteSupportSourceOver f Z).left :=
  inferInstanceAs (IsIntegral (finiteSupportSourceOpen f Z).toScheme)
instance finiteSupportTargetOver_integral : IsIntegral (finiteSupportTargetOver f Z).left :=
  inferInstanceAs (IsIntegral (finiteSupportGoodOpen f Z).toScheme)
instance finiteSupportSourceOver_smooth : Smooth (finiteSupportSourceOver f Z).hom := (finiteSupportGoodOpen_spec f Z).2.2.2.2
instance finiteSupportTargetOver_smooth : Smooth (finiteSupportTargetOver f Z).hom := (finiteSupportGoodOpen_spec f Z).2.2.2.1

def finiteSupportCoverMap : finiteSupportSourceOver f Z ⟶ finiteSupportTargetOver f Z :=
  CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageOverMap f Z) (finiteSupportGoodOpen f Z)

instance finiteSupportCoverMap_finite : IsFinite (finiteSupportCoverMap f Z).left := (finiteSupportGoodOpen_spec f Z).2.1
instance finiteSupportCoverMap_etale : Etale (finiteSupportCoverMap f Z).left := (finiteSupportGoodOpen_spec f Z).2.2.1

local instance : Nonempty ((CycleClass.Thom.Scheme.ProperSupport.Constructions.imageOverMap f Z).left ⁻¹ᵁ finiteSupportGoodOpen f Z) :=
  finiteSupportSourceOpen_nonempty f Z

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportCoverMap_genericPoint :
    (finiteSupportCoverMap f Z).left (genericPoint (finiteSupportSourceOver f Z).left) =
      genericPoint (finiteSupportTargetOver f Z).left :=
  CycleClass.Thom.ProperImage.RestrictionDegree.Constructions.Construction.restrictedSchemeMap_genericPoint (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageOverMap f Z) (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap_genericPoint f Z) (finiteSupportGoodOpen f Z)

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportCoverMap_residueDegree :
    (finiteSupportCoverMap f Z).left.residueDegree (genericPoint (finiteSupportSourceOver f Z).left) =
      f.left.residueDegree (irreducibleSetEquivPoints Z) :=
  (CycleClass.Thom.ProperImage.RestrictionDegree.Constructions.Construction.restrictedSchemeMap_residueDegree (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageOverMap f Z) (finiteSupportGoodOpen f Z)).trans (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap_residueDegree f Z)

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportCoverMap_analytic_proper : IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (finiteSupportCoverMap f Z)) :=
  CycleClass.Thom.Integral.SchemeProper.Constructions.isProperMap_integral (finiteSupportCoverMap f Z)

end

section

/-! The actual finite-etale support cover maps into the original
regular loci by open immersions and preserves the full ambient square. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] (Z : IrreducibleCloseds X.left)

local instance : LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom) := inferInstance
local instance : LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom) := inferInstance

theorem finiteSupportSourceOpen_smoothLocus : finiteSupportSourceOpen f Z ≤ (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom).smoothLocus := by
  let : Smooth ((finiteSupportSourceOpen f Z).ι ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom) :=
    (finiteSupportGoodOpen_spec f Z).2.2.2.2
  exact CycleClass.Thom.ProperImage.RestrictionDegree.Constructions.Construction.open_subset_smoothLocus (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z X.hom) _

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportTargetOpen_smoothLocus : finiteSupportGoodOpen f Z ≤ (CycleClass.Geometric.SupportFiniteType.supportStructureMap (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom).smoothLocus := by
  let : Smooth ((finiteSupportGoodOpen f Z).ι ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom) :=
    (finiteSupportGoodOpen_spec f Z).2.2.2.1
  exact CycleClass.Thom.ProperImage.RestrictionDegree.Constructions.Construction.open_subset_smoothLocus (CycleClass.Geometric.SupportFiniteType.supportStructureMap (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom) _

def finiteSupportSourceToRegular : finiteSupportSourceOver f Z ⟶ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z :=
  CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular X Z (finiteSupportSourceOpen f Z) (finiteSupportSourceOpen_smoothLocus f Z)

def finiteSupportTargetToRegular : finiteSupportTargetOver f Z ⟶ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) :=
  CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) (finiteSupportGoodOpen f Z) (finiteSupportTargetOpen_smoothLocus f Z)

instance finiteSupportSourceToRegular_open : IsOpenImmersion (finiteSupportSourceToRegular f Z).left :=
  inferInstanceAs (IsOpenImmersion (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular X Z (finiteSupportSourceOpen f Z)
    (finiteSupportSourceOpen_smoothLocus f Z)).left)

instance finiteSupportTargetToRegular_open : IsOpenImmersion (finiteSupportTargetToRegular f Z).left :=
  inferInstanceAs (IsOpenImmersion (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) (finiteSupportGoodOpen f Z)
    (finiteSupportTargetOpen_smoothLocus f Z)).left)

theorem finiteSupportSourceToRegular_ambient :
    finiteSupportSourceToRegular f Z ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z =
      CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z) (finiteSupportSourceOpen f Z) ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient X Z :=
  CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular_ambient X Z (finiteSupportSourceOpen f Z) (finiteSupportSourceOpen_smoothLocus f Z)

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportTargetToRegular_ambient :
    finiteSupportTargetToRegular f Z ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) =
      CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)) (finiteSupportGoodOpen f Z) ≫
        CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) :=
  CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.smoothOpenToRegular_ambient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) (finiteSupportGoodOpen f Z) (finiteSupportTargetOpen_smoothLocus f Z)

theorem finiteSupportRegularCover_ambient_square :
    (finiteSupportSourceToRegular f Z ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z) ≫ f =
      finiteSupportCoverMap f Z ≫ (finiteSupportTargetToRegular f Z ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)) := by
  let a : finiteSupportSourceOver f Z ⟶ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z :=
    CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X Z) (finiteSupportSourceOpen f Z)
  let b : finiteSupportTargetOver f Z ⟶ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) :=
    CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)) (finiteSupportGoodOpen f Z)
  let u := CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient X Z
  let v := CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)
  let k := CycleClass.Thom.Scheme.ProperSupport.Constructions.imageOverMap f Z
  have hs : finiteSupportSourceToRegular f Z ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z = a ≫ u :=
    finiteSupportSourceToRegular_ambient f Z
  have ht : finiteSupportTargetToRegular f Z ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) = b ≫ v :=
    finiteSupportTargetToRegular_ambient f Z
  have hk : k ≫ v = u ≫ f := CycleClass.Thom.Scheme.ProperSupport.Constructions.imageOverMap_inclusion f Z
  have hr : finiteSupportCoverMap f Z ≫ b = a ≫ k :=
    CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.restrictedSchemeMap_inclusion (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageOverMap f Z) (finiteSupportGoodOpen f Z)
  exact (congrArg (fun t => t ≫ f) hs).trans
    ((Category.assoc a u f).trans ((congrArg (fun t => a ≫ t) hk.symm).trans
      ((Category.assoc a k v).symm.trans ((congrArg (fun t => t ≫ v) hr.symm).trans
        ((Category.assoc (finiteSupportCoverMap f Z) b v).trans
          (congrArg (fun t => finiteSupportCoverMap f Z ≫ t) ht.symm))))))

theorem finiteSupportSourceOver_dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (finiteSupportSourceOver f Z).hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z).hom :=
  CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpen_dimension X Z (finiteSupportSourceOpen f Z)

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportTargetOver_dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (finiteSupportTargetOver f Z).hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)).hom :=
  CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpen_dimension Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) (finiteSupportGoodOpen f Z)

end

section

/-! The actual finite support cover has the native complex local
diffeomorphisms, countable Hausdorff point spaces, and exactly the
original algebraic residue-field degree on every analytic fiber. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open scoped _root_.Manifold ContDiff

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] (Z : IrreducibleCloseds X.left)

def finiteSupportSourceAmbientMap : finiteSupportSourceOver f Z ⟶ X :=
  finiteSupportSourceToRegular f Z ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z

def finiteSupportTargetAmbientMap : finiteSupportTargetOver f Z ⟶ Y :=
  finiteSupportTargetToRegular f Z ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)

instance finiteSupportSourceAmbientMap_immersion : IsImmersion (finiteSupportSourceAmbientMap f Z).left := by
  change IsImmersion ((finiteSupportSourceToRegular f Z).left ≫ (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient X Z).left)
  infer_instance

instance finiteSupportTargetAmbientMap_immersion : IsImmersion (finiteSupportTargetAmbientMap f Z).left := by
  change IsImmersion ((finiteSupportTargetToRegular f Z).left ≫ (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z)).left)
  infer_instance

instance finiteSupportSourceOver_t2 [T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (finiteSupportSourceOver f Z)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (finiteSupportSourceAmbientMap f Z)).t2Space

instance finiteSupportTargetOver_t2 [T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (finiteSupportTargetOver f Z)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (finiteSupportTargetAmbientMap f Z)).t2Space

instance finiteSupportSourceOver_secondCountable [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] :
    SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (finiteSupportSourceOver f Z)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (finiteSupportSourceAmbientMap f Z)).secondCountableTopology

instance finiteSupportTargetOver_secondCountable [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] :
    SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (finiteSupportTargetOver f Z)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (finiteSupportTargetAmbientMap f Z)).secondCountableTopology

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportCover_dimensions_eq :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (finiteSupportSourceOver f Z).hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (finiteSupportTargetOver f Z).hom := by
  have h := CycleClass.Thom.Integral.MapDimension.Constructions.integral_dominant_dimension (finiteSupportCoverMap f Z).left
    (finiteSupportCoverMap_genericPoint f Z) (finiteSupportTargetOver f Z).hom
  have hw := (finiteSupportCoverMap f Z).w
  rw [hw, Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension,
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension] at h
  exact h.symm

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportCover_fiber_degree (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (finiteSupportTargetOver f Z)) :
    Nat.card (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (finiteSupportCoverMap f Z) ⁻¹' {y}) =
      f.left.residueDegree (irreducibleSetEquivPoints Z) :=
  (CycleClass.Thom.ProperImage.IntrinsicFiberDegree.Constructions.Construction.native_fiber_card_eq_residueDegree (finiteSupportCoverMap f Z) (finiteSupportCoverMap_genericPoint f Z) y).trans
    (finiteSupportCoverMap_residueDegree f Z)

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportCover_localDiffeomorph :
    IsLocalDiffeomorph
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (finiteSupportSourceOver f Z).hom) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (finiteSupportTargetOver f Z).hom) → ℂ)
      ω (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (finiteSupportCoverMap f Z)) :=
  CycleClass.Thom.ProperImage.IntrinsicEtale.Constructions.Construction.isLocalDiffeomorph_nativeScheme_affineEtale (finiteSupportCoverMap f Z)

end

/-! The omitted locus of the actual finite support covering contains
both singular boundaries and has strictly smaller support dimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] (Z : IrreducibleCloseds X.left)

def finiteSupportOmittedBoundary : Closeds Y.left :=
  CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) (finiteSupportGoodOpen f Z)

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportOmittedBoundary_dimension_lt (A : IrreducibleCloseds Y.left)
    (hA : (A : Set Y.left) ⊆ finiteSupportOmittedBoundary f Z) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension A Y.hom < Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom :=
  CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary_dimension_lt Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) (finiteSupportGoodOpen f Z)
    (finiteSupportGoodOpen_spec f Z).1 A hA

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportOmittedBoundary_codimension [IsIntegral Y.left] (q : ℕ)
    (hq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    (A : IrreducibleCloseds Y.left) (hA : (A : Set Y.left) ⊆ finiteSupportOmittedBoundary f Z) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension A Y.hom + (q + 1) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom := by
  have h := finiteSupportOmittedBoundary_dimension_lt f Z A hA
  omega

theorem finiteSupportSourceBoundary_maps_into :
    CycleClass.Geometric.StratumDimension.supportSingularBoundary Z X.hom ⊆ f.left ⁻¹' (finiteSupportOmittedBoundary f Z : Set Y.left) := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap f Z y, ?_, ?_⟩
  · intro hmem
    exact hy (finiteSupportSourceOpen_smoothLocus f Z hmem)
  · exact congrArg (fun k : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ⟶ Y.left => k y) (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap_inclusion f Z)

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportTargetBoundary_subset :
    CycleClass.Geometric.StratumDimension.supportSingularBoundary (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) Y.hom ⊆ finiteSupportOmittedBoundary f Z := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, fun h => hy (finiteSupportTargetOpen_smoothLocus f Z h), rfl⟩

def finiteSupportRetainedOpen : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :=
  CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen Y (finiteSupportOmittedBoundary f Z).compl

theorem finiteSupportRetainedOpen_source_regular :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (finiteSupportRetainedOpen f Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆
      CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z := by
  intro x hx hx'
  have h := finiteSupportSourceBoundary_maps_into f Z hx'
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) ∉ finiteSupportOmittedBoundary f Z at hx
  exact hx h

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportRetainedOpen_target_regular :
    (finiteSupportRetainedOpen f Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) := by
  intro x hx hx'
  exact hx (finiteSupportTargetBoundary_subset f Z hx')

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportSourcePoint_mem_open (y : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z)
    (hy : f.left (CycleClass.Geometric.GenericPoint.reducedSupportι Z y) ∉ finiteSupportOmittedBoundary f Z) :
    y ∈ finiteSupportSourceOpen f Z := by
  by_contra hn
  apply hy
  exact ⟨CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap f Z y, hn,
    congrArg (fun k : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ⟶ Y.left => k y) (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageMap_inclusion f Z)⟩

omit [LocallyOfFiniteType X.hom] in
theorem finiteSupportTargetPoint_mem_open (y : CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z))
    (hy : CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f Z) y ∉ finiteSupportOmittedBoundary f Z) :
    y ∈ finiteSupportGoodOpen f Z := by
  by_contra hn
  exact hy ⟨y, hn, rfl⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Cover.BundleCycles
