import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.AugmentationIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.NegativeIntervalComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AugmentedDualProjectiveResolution

/-! # Parameter Koszul Resolution -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.ParameterKoszulResolution

noncomputable section

/-! The explicitly augmented scalar Koszul complex on regular maximal-ideal parameters is a finite free projective resolution of the residue field. Positive exactness follows from the independently proved regular-local acyclicity argument. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem regularParameterKoszul_exact_negative (rs : List R)
    (hreg : SequenceBasic.RingTheory.Sequence.IsRegular R rs) (hgen : SequenceBasic.Ideal.ofList rs = maximalIdeal R) :
    ∀ i : ℤ, i < 0 → (ScalarKoszul.KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs).ExactAt i := by
  let K := ScalarKoszul.KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs
  let g := rs.length
  let C := HilbertConstruction.Finite.NegativeIntervalComplex.negativeIntervalCochain K g
  have hbound : ∀ i, i < -(g : ℤ) ∨ 0 < i → IsZero (K.X i) :=
    ScalarKoszul.KoszulComplex.scalarKoszulComplex_isZero_X (ModuleCat.of R R) rs
  have hff := ScalarKoszul.FiniteTerms.scalarKoszulComplex_finite_free (ModuleCat.of R R) rs
  have hffC := HilbertConstruction.Finite.NegativeIntervalComplex.negativeIntervalCochain_finite_free K g (fun i => (hff i).1) (fun i => (hff i).2)
  have hfield : Cochain.FieldSupport.CochainFieldSupport C (maximalIdeal R) := by
    apply HilbertConstruction.Finite.NegativeIntervalComplex.negativeIntervalCochain_fieldSupport K g hbound
    intro B _ _ hnot
    have hn : ¬ SequenceBasic.Ideal.ofList rs ≤ RingHom.ker (algebraMap R B) := by simpa only [hgen] using hnot
    obtain ⟨h⟩ := ScalarKoszul.KoszulComplex.scalarKoszulComplex_field_contractible_off_ideal B (ModuleCat.of R R) rs hn
    intro i
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).mpr
    apply (IsZero.iff_id_eq_zero _).mpr
    simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero]
      using h.homologyMap_eq i
  intro i hi
  by_cases hlow : -(g : ℤ) ≤ i
  · let q := (i + g).toNat
    have hq : q < g := by dsimp [q]; omega
    have hqi : (q : ℤ) - g = i := by dsimp [q]; omega
    have hz := LocalCochainAcyclicity.regularLocalCochain_homology_zero_below_regular_parameters g R C
      (fun n => (hffC n).1) (fun n => (hffC n).2) rs rfl hreg hgen hfield q hq
    have he := (HilbertConstruction.Finite.NegativeIntervalComplex.negativeIntervalCochain_exactAt_iff K g q (Nat.le_of_lt hq) hbound).mp
      ((C.exactAt_iff_isZero_homology q).mpr hz)
    simpa only [hqi] using he
  · exact HomologicalComplex.ExactAt.of_isZero (hbound i (Or.inl (lt_of_not_ge hlow)))

def scalarKoszulChainComplex (rs : List R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  (ScalarKoszul.KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs).restriction ComplexShape.embeddingDownNat

def regularParameterKoszulResolution (rs : List R)
    (hreg : SequenceBasic.RingTheory.Sequence.IsRegular R rs) (hgen : SequenceBasic.Ideal.ofList rs = maximalIdeal R) :
    HilbertConstruction.Projective.ResolutionBasic.ProjectiveResolution (ModuleCat.of R (ResidueField R)) := by
  let K := ScalarKoszul.KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs
  let C := scalarKoszulChainComplex rs
  let e := ComplexShape.embeddingDownNat
  letI : K.IsStrictlySupported e := {
    isZero := fun i hi => by
      have hip : 0 < i := by
        by_contra hn
        obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat (le_of_not_gt hn)
        exact hi n rfl
      exact ScalarKoszul.KoszulComplex.scalarKoszulComplex_isZero_X (ModuleCat.of R R) rs i (Or.inr hip) }
  have hproj (n : ℕ) : Projective (C.X n) := by
    have hff := ScalarKoszul.FiniteTerms.scalarKoszulComplex_finite_free (ModuleCat.of R R) rs (-(n : ℤ))
    have : Module.Finite R (C.X n) := hff.1
    have : Module.Free R (C.X n) := hff.2
    infer_instance
  have hexa (n : ℕ) (hn : 0 < n) : C.ExactAt n := by
    apply (SupportedComplexRestriction.strictlySupported_restriction_exactAt_iff e K n).mpr
    exact regularParameterKoszul_exact_negative rs hreg hgen (-(n : ℤ)) (by omega)
  let E : cokernel (C.d 1 0) ≅ ModuleCat.of R (ResidueField R) :=
    ScalarKoszul.AugmentationIdeal.scalarKoszulCokernelQuotientIso rs ≪≫ (Submodule.quotEquivOfEq _ _ hgen).toModuleIso
  exact AugmentedDualProjectiveResolution.projectiveResolutionOfCokernelIso C hproj hexa E

theorem regularParameterKoszulResolution_complex (rs : List R)
    (hreg : SequenceBasic.RingTheory.Sequence.IsRegular R rs) (hgen : SequenceBasic.Ideal.ofList rs = maximalIdeal R) :
    (regularParameterKoszulResolution rs hreg hgen).complex = scalarKoszulChainComplex rs := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.ParameterKoszulResolution
