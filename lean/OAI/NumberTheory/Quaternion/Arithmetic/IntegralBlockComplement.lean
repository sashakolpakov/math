import OAI.NumberTheory.Quaternion.Arithmetic.IntegralCompact
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockDecomposition
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Integral Block Complement -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.IntegralBlockComplement

noncomputable section

/-! Separate a selected block of local factors from the compact integral
groups at all remaining finite places. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*}

abbrev localBlockPoints (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) :=
  ∀ i : {i : ι // p i}, LocalAdeles.LocalPoints G (Sum.inr (v i.val))

abbrev integralBlockComplement (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) :=
  ∀ i : {i : ι // ¬ p i}, LocalAdeles.integralLocalSubgroup G (Sum.inr (v i.val))

instance integralBlockComplementCompact (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) :
    CompactSpace (integralBlockComplement G v p) := by
  let : ∀ i : {i : ι // ¬ p i}, CompactSpace (LocalAdeles.integralLocalSubgroup G (Sum.inr (v i.val))) :=
    fun i => isCompact_iff_compactSpace.mp (IntegralCompact.integralLocalSubgroup_isCompact G (v i.val))
  infer_instance

instance integralBlockComplementTotallyDisconnected (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) :
    TotallyDisconnectedSpace (integralBlockComplement G v p) := by
  let : ∀ i : {i : ι // ¬ p i}, TotallyDisconnectedSpace ((v i.val).adicCompletion F) :=
    fun _ => inferInstance
  let : ∀ i : {i : ι // ¬ p i},
      TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) (LocalAdeles.Completion (Sum.inr (v i.val)))) :=
    fun i => by
      change TotallyDisconnectedSpace (Fin n → Fin n → (v i.val).adicCompletion F)
      infer_instance
  let : ∀ i : {i : ι // ¬ p i}, TotallyDisconnectedSpace (LocalAdeles.LocalPoints G (Sum.inr (v i.val))) :=
    fun i => (IntegralCompact.localPoints_closedEmbedding G (Sum.inr (v i.val))).isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  infer_instance

def insertIntegralBlockComplement (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) :
    integralBlockComplement G v p × localBlockPoints G v p →*
      (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) where
  toFun x i := if h : p i then x.2 ⟨i, h⟩ else (x.1 ⟨i, h⟩).val
  map_one' := by funext i; split_ifs <;> rfl
  map_mul' x y := by
    funext i
    by_cases hi : p i <;> simp [hi]

theorem insertIntegralBlockComplement_continuous (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) :
    Continuous (insertIntegralBlockComplement G v p) := by
  have hc : Continuous (fun x : integralBlockComplement G v p =>
      fun i : {i : ι // ¬ p i} => (x i).val) :=
    Continuous.piMap (fun _ => continuous_subtype_val)
  exact (Homeomorph.piEquivPiSubtypeProd p (fun i => LocalAdeles.LocalPoints G (Sum.inr (v i)))).symm.continuous.comp
    (continuous_snd.prodMk (hc.comp continuous_fst))

def insertLocalBlock (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) :
    localBlockPoints G v p →* (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) where
  toFun x i := if h : p i then x ⟨i, h⟩ else 1
  map_one' := by funext i; split_ifs <;> rfl
  map_mul' x y := by
    funext i
    by_cases hi : p i <;> simp [hi]

theorem insertLocalBlock_continuous (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) : Continuous (insertLocalBlock G v p) := by
  have hc : Continuous (fun b : localBlockPoints G v p =>
      ((1 : integralBlockComplement G v p), b)) := continuous_const.prodMk continuous_id
  exact (insertIntegralBlockComplement_continuous G v p).comp hc

theorem localPrimeBlock_insertIntegralBlockComplement (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (q : ℕ)
    (c : integralBlockComplement G v (fun i => LocalCompletion.residuePrime (v i) = q))
    (b : localBlockPoints G v (fun i => LocalCompletion.residuePrime (v i) = q)) :
    PrimeBlockDecomposition.localPrimeBlock G v q (insertIntegralBlockComplement G v _ (c, b)) =
      insertLocalBlock G v _ b := by
  funext i
  by_cases hi : LocalCompletion.residuePrime (v i) = q <;>
    simp [PrimeBlockDecomposition.localPrimeBlock, insertIntegralBlockComplement, insertLocalBlock, hi]

def restrictLocalBlock (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) :
    (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) →* localBlockPoints G v p where
  toFun g i := g i.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem restrictLocalBlock_continuous (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (p : ι → Prop) : Continuous (restrictLocalBlock G v p) :=
  continuous_pi (fun i => continuous_apply i.val)

theorem insert_restrict_primeBlock (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (q : ℕ) (g : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) :
    insertLocalBlock G v (fun i => LocalCompletion.residuePrime (v i) = q)
      (restrictLocalBlock G v (fun i => LocalCompletion.residuePrime (v i) = q) g) = PrimeBlockDecomposition.localPrimeBlock G v q g := by
  funext i
  by_cases hi : LocalCompletion.residuePrime (v i) = q <;>
    simp [insertLocalBlock, restrictLocalBlock, PrimeBlockDecomposition.localPrimeBlock, hi]

end

end OAI.NumberTheory.Quaternion.Arithmetic.IntegralBlockComplement
