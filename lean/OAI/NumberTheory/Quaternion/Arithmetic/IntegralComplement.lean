import OAI.NumberTheory.Quaternion.Arithmetic.IntegralCompact

/-! # Integral Complement -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.IntegralComplement

noncomputable section

/-! One local factor together with the compact integral groups at the
other selected places, and its continuous inclusion into the product. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*}

abbrev integralComplement (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : ι → HeightOneSpectrum (𝓞 F)) (i : ι) :=
  ∀ j : {j : ι // j ≠ i}, LocalAdeles.integralLocalSubgroup G (Sum.inr (v j.val))

instance integralComplementCompact (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (i : ι) : CompactSpace (integralComplement G v i) := by
  let : ∀ j : {j : ι // j ≠ i}, CompactSpace (LocalAdeles.integralLocalSubgroup G (Sum.inr (v j.val))) :=
    fun j => isCompact_iff_compactSpace.mp (IntegralCompact.integralLocalSubgroup_isCompact G (v j.val))
  infer_instance

def insertIntegralComplement (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (i : ι) :
    (integralComplement G v i × LocalAdeles.LocalPoints G (Sum.inr (v i))) →*
      (∀ j, LocalAdeles.LocalPoints G (Sum.inr (v j))) where
  toFun x j := if h : j = i then h.symm ▸ x.2 else (x.1 ⟨j, h⟩).val
  map_one' := by
    funext j
    dsimp only
    split_ifs with h
    · subst j; rfl
    · rfl
  map_mul' x y := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]

@[simp] theorem insertIntegralComplement_self (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (i : ι)
    (x : integralComplement G v i × LocalAdeles.LocalPoints G (Sum.inr (v i))) :
    insertIntegralComplement G v i x i = x.2 := by
  simp [insertIntegralComplement]

theorem insertIntegralComplement_continuous (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : ι → HeightOneSpectrum (𝓞 F)) (i : ι) : Continuous (insertIntegralComplement G v i) := by
  have hc : Continuous (fun x : integralComplement G v i =>
      fun j : {j : ι // j ≠ i} => (x j).val) :=
    Continuous.piMap (fun _ => continuous_subtype_val)
  exact (Homeomorph.piSplitAt i (fun j => LocalAdeles.LocalPoints G (Sum.inr (v j)))).symm.continuous.comp
    (continuous_snd.prodMk (hc.comp continuous_fst))

end

end OAI.NumberTheory.Quaternion.Arithmetic.IntegralComplement
