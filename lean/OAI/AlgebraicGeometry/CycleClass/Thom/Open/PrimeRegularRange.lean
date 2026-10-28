import OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularPointCriterion

/-! # Prime Regular Range -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange.Constructions.SupportMap

/-! The actual open map from a reduced support to its reduced ambient closure preserves the original inclusion and intrinsic smooth locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportClosure.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularPointCriterion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem smoothLocus_congr {A B : Scheme} (f g : A ⟶ B)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) : f.smoothLocus = g.smoothLocus := by
  subst g
  rfl

variable {X S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType S.hom]
  (a : X ⟶ S) [IsOpenImmersion a.left] [QuasiCompact a.left] (Z : IrreducibleCloseds X.left)

local instance : IsOpenImmersion (Thom.Scheme.OpenSupportClosure.Constructions.toClosureOver a Z).left :=
  inferInstanceAs (IsOpenImmersion (Thom.Scheme.OpenSupportClosure.Constructions.toClosure a Z))
local instance : LocallyOfFinitePresentation (Thom.Scheme.RegularSupport.Constructions.supportOver X Z).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Geometric.SupportFiniteType.supportStructureMap Z X.hom))
local instance : LocallyOfFinitePresentation (Thom.Scheme.RegularSupport.Constructions.supportOver S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z)).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Geometric.SupportFiniteType.supportStructureMap (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z) S.hom))

omit [LocallyOfFiniteType X.hom] [LocallyOfFiniteType S.hom] [QuasiCompact a.left] in
theorem closureSupport_analytic_preimage :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a ⁻¹' Set.range (Thom.Scheme.RegularSupport.Constructions.supportInclusion S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z)) =
      Set.range (Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z) := by
  rw [Thom.Scheme.RegularSupport.Constructions.supportInclusion_range, Thom.Scheme.RegularSupport.Constructions.supportInclusion_range]
  ext x
  exact Set.ext_iff.mp (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport_preimage a Z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x)

omit [LocallyOfFiniteType X.hom] [LocallyOfFiniteType S.hom] [IsOpenImmersion a.left] in
theorem closureSupportMap_point (t : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Thom.Scheme.RegularSupport.Constructions.supportOver X Z)) :
    Thom.Scheme.RegularSupport.Constructions.supportInclusion S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Thom.Scheme.OpenSupportClosure.Constructions.toClosureOver a Z) t) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a (Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z t) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (Thom.Scheme.OpenSupportClosure.Constructions.toClosureOver a Z) (Thom.Scheme.RegularSupport.Constructions.supportToAmbient S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z)) t).symm.trans
    ((congrArg (fun f => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f t) (Thom.Scheme.OpenSupportClosure.Constructions.toClosureOver_ambient a Z)).trans
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (Thom.Scheme.RegularSupport.Constructions.supportToAmbient X Z) a t))

theorem closureSupportMap_smoothLocus : (Thom.Scheme.OpenSupportClosure.Constructions.toClosureOver a Z).left ⁻¹ᵁ
    (Thom.Scheme.RegularSupport.Constructions.supportOver S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z)).hom.smoothLocus = (Thom.Scheme.RegularSupport.Constructions.supportOver X Z).hom.smoothLocus := by
  have h := (Thom.Scheme.OpenSupportClosure.Constructions.toClosureOver a Z).left.preimage_smoothLocus_eq (Thom.Scheme.RegularSupport.Constructions.supportOver S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z)).hom
  exact h.trans (smoothLocus_congr _ _ (Thom.Scheme.OpenSupportClosure.Constructions.toClosureOver a Z).w)

theorem closureSupportMap_regular_iff (t : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Thom.Scheme.RegularSupport.Constructions.supportOver X Z)) :
    Thom.Scheme.RegularSupport.Constructions.supportInclusion S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Thom.Scheme.OpenSupportClosure.Constructions.toClosureOver a Z) t) ∈
        Set.range (Thom.Scheme.RegularSupport.Constructions.regularInclusion S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z)) ↔
      Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z t ∈ Set.range (Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z) := by
  rw [Thom.Scheme.RegularPointCriterion.Constructions.supportPoint_regular_iff, Thom.Scheme.RegularPointCriterion.Constructions.supportPoint_regular_iff]
  exact (congrArg (fun O : (Thom.Scheme.RegularSupport.Constructions.supportOver X Z).left.Opens => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying t ∈ O)
    (closureSupportMap_smoothLocus a Z)).to_iff

theorem closure_regularInclusion_preimage :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a ⁻¹' Set.range (Thom.Scheme.RegularSupport.Constructions.regularInclusion S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z)) =
      Set.range (Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z) := by
  ext y
  constructor
  · intro hy
    have hf := Thom.Scheme.RegularSupport.Constructions.regularInclusion_subset S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z) hy
    have hx := (Set.ext_iff.mp (closureSupport_analytic_preimage a Z) y).mp hf
    obtain ⟨t, rfl⟩ := hx
    apply (closureSupportMap_regular_iff a Z t).mp
    exact (congrArg (fun v => v ∈ Set.range (Thom.Scheme.RegularSupport.Constructions.regularInclusion S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z)))
      (closureSupportMap_point a Z t)).mpr hy
  · intro hy
    obtain ⟨t, rfl⟩ := Thom.Scheme.RegularSupport.Constructions.regularInclusion_subset X Z hy
    have ht := (closureSupportMap_regular_iff a Z t).mpr hy
    exact (congrArg (fun v => v ∈ Set.range (Thom.Scheme.RegularSupport.Constructions.regularInclusion S (Thom.Scheme.OpenSupportClosure.Constructions.closureSupport a Z)))
      (closureSupportMap_point a Z t)).mp ht

end AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange.Constructions.SupportMap

namespace AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange.Constructions

/-! The regular analytic image of a prime divisor commutes with restriction to an actual open subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange.Constructions.SupportMap OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [LocallyOfFiniteType X.hom]
  [IsIntegral S.left] [LocallyOfFiniteType S.hom] (a : X ⟶ S) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (z : {x : X.left // Order.coheight x = 1})

omit [IsIntegral X.left] [IsIntegral S.left] in
theorem regularInclusion_preimage :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a ⁻¹' Set.range (Thom.Scheme.RegularSupport.Constructions.regularInclusion S (SchemeDivisor.Purity.Constructions.primeSupport S (PrimeSupport.Constructions.ambientPrime a z))) =
      Set.range (Thom.Scheme.RegularSupport.Constructions.regularInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) := by
  rw [PrimeSupport.Constructions.ambientPrimeSupport_eq_closure]
  exact SupportMap.closure_regularInclusion_preimage a (SchemeDivisor.Purity.Constructions.primeSupport X z)

end AlgebraicGeometry.CycleClass.Thom.Open.PrimeRegularRange.Constructions

end

end OAI
