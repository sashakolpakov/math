import OAI.RepresentationTheory.Theta.AdelicSupport
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # Integral Adeles -/

namespace OAI.RepresentationTheory.Theta.IntegralAdeles.PoissonAutomorphyConstruction

noncomputable section

/-! Integral finite adeles as a product of compact local integer rings. -/

open scoped Classical RestrictedProduct
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

def integralProductHomeomorph :
    (∀ v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, v.adicCompletionIntegers ℚ) ≃ₜ AdelicSupport.PoissonAutomorphyConstruction.integralAdele :=
  (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace => v.adicCompletion ℚ)
    (A := fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    (𝓕 := Filter.cofinite)).toHomeomorph.trans
      (Homeomorph.setCongr (by
        rw [RestrictedProduct.range_structureMap]
        rfl))

theorem integralProductHomeomorph_apply
    (x : ∀ v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, v.adicCompletionIntegers ℚ) (v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    (integralProductHomeomorph x).val v = (x v).val := rfl

instance localIntegerCompact (v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    CompactSpace (v.adicCompletionIntegers ℚ) := by
  let : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm.compactSpace

instance integralAdeleCompact : CompactSpace AdelicSupport.PoissonAutomorphyConstruction.integralAdele :=
  integralProductHomeomorph.compactSpace

theorem isCompact_integralAdele : IsCompact (AdelicSupport.PoissonAutomorphyConstruction.integralAdele : Set PoissonAutomorphyNormalizationData.AQf) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace AdelicSupport.PoissonAutomorphyConstruction.integralAdele))

theorem localInteger_dense_intCast (v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    DenseRange (fun n : ℤ => (n : v.adicCompletionIntegers ℚ)) := by
  let : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  have h := e.symm.surjective.denseRange.comp PadicInt.denseRange_intCast e.symm.continuous
  simpa only [Function.comp_def, map_intCast] using h

end

end OAI.RepresentationTheory.Theta.IntegralAdeles.PoissonAutomorphyConstruction
