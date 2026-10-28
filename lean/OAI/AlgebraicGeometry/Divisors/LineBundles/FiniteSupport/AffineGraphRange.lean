import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.OpenChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.SupportRange

/-! # Affine Graph Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphRange.BundleCycles

noncomputable section

/-! The lifted support graph is exactly the full support graph in the actual affine source over the retained open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.GraphEmbedding.Constructions

variable {S Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (g : S ⟶ Y) [IsFinite g.left]
  (Z : IrreducibleCloseds S.left)
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ S) [IsOpenImmersion a.left]

def finiteSupportAffineSupportSet : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion S Z)

variable [IsAffine X.left] {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

def finiteSupportAffineFullGraph (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) × (Fin d → ℂ) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y), CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f y)

variable (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

def finiteSupportAffineGraphImage : Set (U × (Fin d → ℂ)) :=
  {u | ∃ y, y ∈ finiteSupportAffineSupportSet Z a ∧ finiteSupportAffineFullGraph g a f y = (u.1.val, u.2)}

omit [IsAffine X.left] in
theorem finiteSupportAffineLift_ambient (x : FiniteAffine.OpenChart.BundleCycles.finiteSupportLocalSource g Z U) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineLift g Z U a hcover x)) =
      CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase (Cover.BundleCycles.finiteSupportCoverMap g Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) x.val :=
  (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g) (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineLift_commutes g Z U a hcover x)).trans
    (congrFun (FiniteAffine.OpenChart.BundleCycles.finiteSupportCover_liftBase_eq g Z) x.val)

theorem finiteSupportAffineGraph_range (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆ Cover.BundleCycles.finiteSupportRetainedOpen g Z) :
    Set.range (CycleClass.Thom.EtaleLocalGraph.Constructions.localGraph (Cover.BundleCycles.finiteSupportCoverMap g Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) U
      (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineCoordinates g Z U a hcover f)) = finiteSupportAffineGraphImage g Z a f U := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineLift g Z U a hcover x, ?_, ?_⟩
    · exact (congrArg (fun y => y ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion S Z)) (FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineLift_commutes g Z U a hcover x)).mpr
        (SupportRange.BundleCycles.finiteSupportSourceAmbientMap_range_subset_support g Z ⟨x.val, rfl⟩)
    · exact Prod.ext (finiteSupportAffineLift_ambient g Z a U hcover x) rfl
  · rintro ⟨y, hy, he⟩
    have he1 := congrArg (Prod.fst : (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) × (Fin d → ℂ) → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) he
    have hyU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) ∈ U :=
      (congrArg (fun v : (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) => v ∈ U) he1).mpr u.1.property
    obtain ⟨l, hl⟩ := SupportRange.BundleCycles.finiteSupportFullSupport_point_mem_cover_range g Z (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) hy (hU hyU)
    have hb : CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase (Cover.BundleCycles.finiteSupportCoverMap g Z) (Cover.BundleCycles.finiteSupportTargetAmbientMap g Z) l =
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a y) :=
      (congrFun (FiniteAffine.OpenChart.BundleCycles.finiteSupportCover_liftBase_eq g Z) l).symm.trans
        (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g) hl)
    have hlU := (congrArg (fun v : (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) => v ∈ U) hb).mpr hyU
    let x : FiniteAffine.OpenChart.BundleCycles.finiteSupportLocalSource g Z U := ⟨l, hlU⟩
    have hxy : FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineLift g Z U a hcover x = y :=
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion a).injective
        ((FiniteAffine.OpenChart.BundleCycles.finiteSupportAffineLift_commutes g Z U a hcover x).trans hl)
    refine ⟨x, Prod.ext (Subtype.ext (hb.trans he1)) ?_⟩
    exact (congrArg (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) hxy).trans
      (congrArg (Prod.snd : (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) × (Fin d → ℂ) → (Fin d → ℂ)) he)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.AffineGraphRange.BundleCycles
