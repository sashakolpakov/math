import OAI.NumberTheory.Quaternion.Arithmetic.SpanLocal

/-! # Ordered Product Derivative -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.OrderedProductDerivative

noncomputable section

section

/-! The first derivative of an ordered, possibly noncommutative product
at a point where every factor equals one. -/

open scoped Classical

theorem orderedProduct_eq_one
    {ι E A : Type*} [Monoid A] (l : List ι) (f : ι → E → A) (x : E)
    (hf : ∀ i ∈ l, f i x = 1) : (l.map (fun i => f i x)).prod = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, hf i (List.mem_cons_self ..),
      ih (fun j hj => hf j (List.mem_cons_of_mem i hj)), one_mul]

theorem hasStrictFDerivAt_orderedProduct_one
    {κ ι E A : Type*} [NontriviallyNormedField κ]
    [NormedAddCommGroup E] [NormedSpace κ E]
    [NormedRing A] [NormedAlgebra κ A]
    (l : List ι) (f : ι → E → A) (f' : ι → E →L[κ] A) (x : E)
    (hf : ∀ i ∈ l, HasStrictFDerivAt (f i) (f' i) x)
    (h1 : ∀ i ∈ l, f i x = 1) :
    HasStrictFDerivAt (fun y => (l.map (fun i => f i y)).prod)
      (l.map f').sum x := by
  induction l with
  | nil => exact hasStrictFDerivAt_const 1 x
  | cons i l ih =>
    have hi := hf i (List.mem_cons_self ..)
    have ht := ih (fun j hj => hf j (List.mem_cons_of_mem i hj))
      (fun j hj => h1 j (List.mem_cons_of_mem i hj))
    have hp := hi.mul' ht
    convert! hp using 1
    rw [List.map_cons, List.sum_cons, h1 i (List.mem_cons_self ..),
      orderedProduct_eq_one l f x (fun j hj => h1 j (List.mem_cons_of_mem i hj))]
    simp only [MulOpposite.op_one, one_smul, add_comm]

end

/-! Exponential and logarithm derivatives over the closed prime local
field, with scalar actions made explicit. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain

theorem hasStrictFDerivAt_id_restrictScalars
    {κ K E : Type*} [NontriviallyNormedField κ] [NontriviallyNormedField K]
    [NormedAlgebra κ K] [NormedAddCommGroup E] [NormedSpace K E]
    [NormedSpace κ E] [IsScalarTower κ K E] {f : E → E} {x : E}
    (hf : HasStrictFDerivAt f (ContinuousLinearMap.id K E) x) :
    HasStrictFDerivAt f (ContinuousLinearMap.id κ E) x := by
  convert! hf.restrictScalars κ using 1

attribute [local instance] TangentBracket.finiteClosedPrimeNontriviallyNormedField

variable {F : Type} [Field F] [NumberField F]

@[instance_reducible]
def finitePrimeNormedSpace (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedAddCommGroup A] [NormedSpace (v.adicCompletion F) A] :
    NormedSpace (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A where
  norm_smul_le a x := norm_smul_le (a : v.adicCompletion F) x

@[instance_reducible]
def finitePrimeNormedAlgebra (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] :
    NormedAlgebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A :=
  NormedAlgebra.restrictScalars (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
    (v.adicCompletion F) A

attribute [local instance 50] finitePrimeNormedAlgebra

theorem finitePrimeScalarTower (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] :
    IsScalarTower (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) A where
  smul_assoc a b x := smul_assoc (a : v.adicCompletion F) b x

attribute [local instance] finitePrimeScalarTower

theorem finiteExp_hasStrictFDerivAt_prime (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    HasStrictFDerivAt (NormedSpace.exp : A → A)
      (ContinuousLinearMap.id (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A) 0 := by
  refine @hasStrictFDerivAt_id_restrictScalars
    (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) A
    _ _ _ _ _ _ ?_ _ _ (LocalCompletion.finite_exponential_hasStrictFDerivAt v A)
  constructor
  intro a b x
  change ((a : v.adicCompletion F) * b) • x = (a : v.adicCompletion F) • (b • x)
  exact mul_smul _ _ _

theorem finiteLog_hasStrictFDerivAt_prime (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    HasStrictFDerivAt (SpanLocal.finiteLocalLog v A)
      (ContinuousLinearMap.id (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A) 1 := by
  refine @hasStrictFDerivAt_id_restrictScalars
    (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) A
    _ _ _ _ _ _ ?_ _ _ (SpanLocal.finiteLocalLog_hasStrictFDerivAt v A)
  constructor
  intro a b x
  change ((a : v.adicCompletion F) * b) • x = (a : v.adicCompletion F) • (b • x)
  exact mul_smul _ _ _

end

end OAI.NumberTheory.Quaternion.Arithmetic.OrderedProductDerivative
