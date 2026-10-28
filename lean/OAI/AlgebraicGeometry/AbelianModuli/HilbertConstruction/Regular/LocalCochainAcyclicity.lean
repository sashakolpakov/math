import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.FieldSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.ParameterQuotient
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CohomologyRegularity

/-! # Local Cochain Acyclicity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.LocalCochainAcyclicity

noncomputable section

/-! A finite free nonnegative cochain complex over a Noetherian local ring, acyclic on every field-valued coefficient map away from the closed point, has zero cohomology below the length of a regular sequence generating the maximal ideal. The proof inducts by actual scalar reduction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
open scoped TensorProduct
universe u

private theorem cochain_homology_finite_of_finite_term
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) [Module.Finite R (C.X q)] :
    Module.Finite R (C.homology q) := by
  let S := C.sc q
  have : Module.Finite R S.X₂ := inferInstanceAs (Module.Finite R (C.X q))
  have : Module.Finite R S.g.hom.ker := inferInstance
  have : Module.Finite R S.moduleCatLeftHomologyData.H :=
    inferInstanceAs (Module.Finite R (S.g.hom.ker ⧸ LinearMap.range S.moduleCatToCycles))
  exact Module.Finite.equiv S.moduleCatHomologyIso.symm.toLinearEquiv

theorem regularLocalCochain_homology_zero_below_regular_parameters (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (C : CochainComplex (ModuleCat.{u} R) ℕ)
      (_ : ∀ q, Module.Finite R (C.X q)) (_ : ∀ q, Module.Free R (C.X q))
      (rs : List R) (_ : rs.length = n) (_ : SequenceBasic.RingTheory.Sequence.IsRegular R rs)
      (_ : SequenceBasic.Ideal.ofList rs = maximalIdeal R)
      (_ : Cochain.FieldSupport.CochainFieldSupport C (maximalIdeal R)),
      ∀ q, q < n → IsZero (C.homology q) := by
  induction n with
  | zero =>
    intro R _ _ _ C _ _ rs _ _ _ _ q hq
    exact (Nat.not_lt_zero q hq).elim
  | succ n ih =>
    intro R _ _ _ C hfin hfree rs hlen hreg hgen hfield q hq
    cases rs with
    | nil => simp at hlen
    | cons r rs =>
      have hr : r ∈ maximalIdeal R := by
        rw [← hgen]
        exact Ideal.subset_span (by simp)
      have hregular : IsSMulRegular R r := ((SequenceBasic.RingTheory.Sequence.isRegular_cons_iff R r rs).mp hreg).1
      have hterms (i : ℕ) : IsSMulRegular (C.X i) r := by
        have : Module.Free R (C.X i) := hfree i
        exact ((TensorProduct.rid R (C.X i)).isSMulRegular_congr r).mp (hregular.lTensor (C.X i))
      have : Module.Finite R (C.X q) := hfin q
      have : Module.Finite R (C.homology q) := cochain_homology_finite_of_finite_term C q
      have hSupport := hfield.homology_support hfin hfree q
      cases q with
      | zero =>
        have : Subsingleton (C.homology 0) :=
          SupportedRegularModuleVanishing.finiteSupportedModule_subsingleton_of_regularElement (maximalIdeal R) hSupport r hr
            (Scalar.CohomologyRegularity.cochain_homology_zero_regular C r (hterms 0))
        exact ModuleCat.isZero_of_subsingleton _
      | succ m =>
        let J : Ideal R := Ideal.span {r}
        let S := R ⧸ J
        have hJle : J ≤ maximalIdeal R := by
          apply Ideal.span_le.mpr
          rintro x rfl
          exact hr
        have hJne : J ≠ ⊤ := by
          intro heq
          exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_unique (heq ▸ hJle))
        let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hJne
        let : IsLocalRing S := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
        let CS := ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R S).mapHomologicalComplex (.up ℕ)).obj C
        have hfinS (i : ℕ) : Module.Finite S (CS.X i) := by
          have : Module.Finite R (C.X i) := hfin i
          exact inferInstanceAs (Module.Finite S (S ⊗[R] C.X i))
        have hfreeS (i : ℕ) : Module.Free S (CS.X i) := by
          have : Module.Free R (C.X i) := hfree i
          exact inferInstanceAs (Module.Free S (S ⊗[R] C.X i))
        obtain ⟨hregS, hgenS⟩ := ParameterQuotient.regular_parameters_quotient r rs hreg hgen
        have hmap : (maximalIdeal R).map (Ideal.Quotient.mk J) = maximalIdeal S :=
          IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
        have hfieldS : Cochain.FieldSupport.CochainFieldSupport CS (maximalIdeal S) := by
          have hh := hfield.quotient J
          rw [hmap] at hh
          exact hh
        have hlenS : (rs.map (Ideal.Quotient.mk J)).length = n := by
          have hlen' : rs.length = n := Nat.succ.inj hlen
          simpa only [List.length_map] using hlen'
        have hm : m < n := Nat.lt_of_succ_lt_succ hq
        have hzeroS := ih S CS hfinS hfreeS (rs.map (Ideal.Quotient.mk J)) hlenS hregS hgenS hfieldS m hm
        have hprev : (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex S C).ExactAt m :=
          (Base.ChangeTensorExactness.baseChange_exactAt_iff_tensor C m).mp ((CS.exactAt_iff_isZero_homology m).mpr hzeroS)
        exact Scalar.CohomologyRegularity.cochain_homology_succ_zero_of_supported_reduction_exact C (maximalIdeal R) r hr
          hterms m hSupport hprev

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.LocalCochainAcyclicity
