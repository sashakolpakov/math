import OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportClosure
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity

/-! # Prime Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions

noncomputable section

/-! Prime divisors on an actual open subscheme retain their genuine codimension-one points, full supports, and literal scheme orders in the ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportClosure.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [LocallyOfFiniteType X.hom]
  [IsIntegral S.left] [LocallyOfFiniteType S.hom] (a : X ⟶ S) [IsOpenImmersion a.left]
  (z : {x : X.left // Order.coheight x = 1})

def ambientPrime : {x : S.left // Order.coheight x = 1} :=
  ⟨a.left z.val, (coheight_eq_of_isOpenImmersion a.left).trans z.property⟩

omit [IsIntegral X.left] [LocallyOfFiniteType X.hom] [IsIntegral S.left] [LocallyOfFiniteType S.hom] in
theorem primeSupport_preimage : a.left ⁻¹' (SchemeDivisor.Purity.Constructions.primeSupport S (ambientPrime a z) : Set S.left) =
    (SchemeDivisor.Purity.Constructions.primeSupport X z : Set X.left) := by
  change a.left ⁻¹' closure {a.left z.val} = closure {z.val}
  have he := a.left.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image ({z.val} : Set X.left)
  simpa only [Set.image_singleton] using he.symm

omit [IsIntegral X.left] [LocallyOfFiniteType X.hom] [IsIntegral S.left] [LocallyOfFiniteType S.hom] in
theorem primeSupport_analytic_preimage :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a ⁻¹' Set.range (Scheme.RegularSupport.Constructions.supportInclusion S (SchemeDivisor.Purity.Constructions.primeSupport S (ambientPrime a z))) =
      Set.range (Scheme.RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) := by
  rw [Scheme.RegularSupport.Constructions.supportInclusion_range, Scheme.RegularSupport.Constructions.supportInclusion_range]
  ext x
  exact Set.ext_iff.mp (primeSupport_preimage a z) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x)

local instance : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
local instance : IsLocallyNoetherian S.left := LocallyOfFiniteType.isLocallyNoetherian S.hom

theorem ambientPrime_ord (g : S.left.functionField) :
    X.left.ord (RationalOrderTransport.Constructions.openFunctionFieldMap a.left g) z.val = S.left.ord g (ambientPrime a z).val :=
  RationalOrderTransport.Constructions.ord_openImmersion a.left g z.val

variable [QuasiCompact a.left]

omit [IsIntegral X.left] [LocallyOfFiniteType X.hom] [IsIntegral S.left] [LocallyOfFiniteType S.hom] in
theorem ambientPrimeSupport_eq_closure : SchemeDivisor.Purity.Constructions.primeSupport S (ambientPrime a z) = Scheme.OpenSupportClosure.Constructions.closureSupport a (SchemeDivisor.Purity.Constructions.primeSupport X z) := by
  apply irreducibleSetEquivPoints.injective
  have he := Scheme.OpenSupportClosure.Constructions.closureSupport_genericPoint a (SchemeDivisor.Purity.Constructions.primeSupport X z)
  simpa only [SchemeDivisor.Purity.Constructions.primeSupport, OrderIso.apply_symm_apply, ambientPrime] using he.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions
