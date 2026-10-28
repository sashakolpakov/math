import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.GraphDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle

/-! # Prime Image Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeImagePoint.BundleCycles

noncomputable section

/-! An actual source prime divisor under an open inclusion and finite map yields its literal image point in the required dimension grade. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] (k : S ⟶ N) [IsFinite k.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ S) [IsOpenImmersion a.left]
  (z : {x : X.left // Order.coheight x = 1})

omit [AlgebraicGeometry.IsIntegral S.left] [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] in
theorem finitePrimeImage_supportPoint :
    irreducibleSetEquivPoints (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))) = k.left (a.left z.val) := by
  have h := CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport_genericPoint k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z))
  simpa only [CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport, OrderIso.apply_symm_apply, CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime] using h

omit [AlgebraicGeometry.IsIntegral S.left] [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] in
theorem finitePrimeImage_support_eq :
    irreducibleSetEquivPoints.symm (k.left (a.left z.val)) = CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) :=
  (congrArg irreducibleSetEquivPoints.symm (finitePrimeImage_supportPoint k a z)).symm.trans
    (irreducibleSetEquivPoints.symm_apply_apply _)

variable (n : ℕ) (hn : n + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom)

def finitePrimeImagePoint : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint N.hom n :=
  ⟨k.left (a.left z.val), by
    rw [finitePrimeImage_support_eq k a z]
    have h := FiniteAffine.GraphDimension.BundleCycles.finitePrimeImage_dimension k p hp (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)
    omega⟩

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] in
theorem finitePrimeImagePoint_val : (finitePrimeImagePoint k p hp a z n hn).val = k.left (a.left z.val) := rfl

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] in
theorem finitePrimeImagePoint_support :
    irreducibleSetEquivPoints.symm (finitePrimeImagePoint k p hp a z n hn).val =
      CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (CycleClass.Thom.Open.PrimeSupport.Constructions.ambientPrime a z)) := finitePrimeImage_support_eq k a z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeImagePoint.BundleCycles
