import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Adelic Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Finite adelic coefficients are Q-finite-adeles tensor E. Conjugation
acts on the E factor. This is the scalar-extension model of restriction
of scalars; the topology is the usual finite product topology in a Q-basis.
The completed lattice is the Z-hat span of the actual integral lattice. -/

open scoped Classical TensorProduct
open IsDedekindDomain

abbrev AdelicData.RationalFiniteAdeles := IsDedekindDomain.FiniteAdeleRing ℤ ℚ

def AdelicData.integralFiniteAdeles : Subring AdelicData.RationalFiniteAdeles where
  carrier := {a | ∀ v : HeightOneSpectrum ℤ, a v ∈ v.adicCompletionIntegers ℚ}
  zero_mem' v := (v.adicCompletionIntegers ℚ).zero_mem
  one_mem' v := (v.adicCompletionIntegers ℚ).one_mem
  add_mem' ha hb v := (v.adicCompletionIntegers ℚ).toSubring.add_mem (ha v) (hb v)
  mul_mem' ha hb v := (v.adicCompletionIntegers ℚ).toSubring.mul_mem (ha v) (hb v)
  neg_mem' ha v := (v.adicCompletionIntegers ℚ).toSubring.neg_mem (ha v)

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

abbrev AdelicData.FiniteCoefficients := AdelicData.RationalFiniteAdeles ⊗[ℚ] E

def AdelicData.finiteCoefficientEmbedding : E →ₐ[ℚ] AdelicData.FiniteCoefficients E :=
  Algebra.TensorProduct.includeRight

def AdelicData.finiteCoefficientConjugation : AdelicData.FiniteCoefficients E →ₐ[ℚ] AdelicData.FiniteCoefficients E :=
  Algebra.TensorProduct.map (AlgHom.id ℚ AdelicData.RationalFiniteAdeles)
    (NumberField.IsCMField.complexConj E).toRingHom.toRatAlgHom

instance AdelicData.finiteCoefficientTopology : TopologicalSpace (AdelicData.FiniteCoefficients E) :=
  TopologicalSpace.induced ((Module.finBasis ℚ E).baseChange AdelicData.RationalFiniteAdeles).equivFun
    inferInstance

instance AdelicData.finiteCoefficientIntegralAlgebra : Algebra AdelicData.integralFiniteAdeles (AdelicData.FiniteCoefficients E) :=
  ((algebraMap AdelicData.RationalFiniteAdeles (AdelicData.FiniteCoefficients E)).comp AdelicData.integralFiniteAdeles.subtype).toAlgebra

def AdelicData.finiteVectorEmbedding (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE (AdelicData.FiniteCoefficients E) :=
  fun i => AdelicData.finiteCoefficientEmbedding E (x i)

def AdelicData.finiteHermitian (b : E) (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE (AdelicData.FiniteCoefficients E)) : AdelicData.FiniteCoefficients E :=
  ∑ i : Fin 3, (if i = 2 then AdelicData.finiteCoefficientEmbedding E b else 1) *
    x i * AdelicData.finiteCoefficientConjugation E (y i)

variable {E} {s : ℕ} (P : Datum.RankThreePELDatum E s)

def Datum.RankThreePELDatum.completedLattice : Submodule AdelicData.integralFiniteAdeles (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE (AdelicData.FiniteCoefficients E)) :=
  Submodule.span AdelicData.integralFiniteAdeles
    (AdelicData.finiteVectorEmbedding E '' (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)))

abbrev Datum.RankThreePELDatum.FiniteSpecialUnitary := Groups.specialUnitarySubgroup (R := AdelicData.FiniteCoefficients E)
  (AdelicData.finiteHermitian E P.b)

instance Datum.RankThreePELDatum.finiteSpecialUnitaryTopology : TopologicalSpace P.FiniteSpecialUnitary :=
  TopologicalSpace.induced
    (fun g : P.FiniteSpecialUnitary =>
      fun i j : Fin 3 => g.val (Pi.single j 1) i) inferInstance

def Datum.RankThreePELDatum.adelicPrincipalLevel (N : ℕ) : Subgroup P.FiniteSpecialUnitary :=
  (Groups.principalLatticeSubgroup (R := AdelicData.FiniteCoefficients E) P.completedLattice.toAddSubgroup N).comap
    (Groups.specialUnitarySubgroup (R := AdelicData.FiniteCoefficients E) (AdelicData.finiteHermitian E P.b)).subtype

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
