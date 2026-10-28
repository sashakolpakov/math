import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension
import OAI.Algebra.Foundations.PolynomialCatenaryT
import OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles

/-! # Cycle Codimension -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleCodimension

noncomputable section

/-! # The original point codimension equals the actual function-field codimension -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension.Construction

/-- The arbitrary-height version of the finite-type prime quotient dimension formula. -/
theorem finiteType_height_trdeg (K A : Type) [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (q : Ideal A) [q.IsPrime]
    (p : ℕ) (hq : q.height = p) :
    (Algebra.trdeg K (A ⧸ q)).toNat + p = (Algebra.trdeg K A).toNat := by
  obtain ⟨n, f, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let P := MvPolynomial (Fin n) K
  let : Algebra P A := f.toRingHom.toAlgebra
  let : Algebra.IsIntegral P A := ⟨hint⟩
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  let r : Ideal P := q.comap (algebraMap P A)
  have hr : r.height = p := by
    have h := DivisorClass.Chern.IntegralDimension.Construction.integral_comap_height (R := P) (S := A) ⟨q, inferInstance⟩
    have h' : q.height = r.height := by
      rw [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h
      exact h
    exact h'.symm.trans hq
  have hquot : ringKrullDim (A ⧸ q) = ringKrullDim (P ⧸ r) :=
    DivisorClass.Chern.IntegralDimension.Construction.integral_ringKrullDim_eq (R := P ⧸ r) (S := A ⧸ q) Ideal.algebraMap_quotient_injective
  have hdim : (p : WithBot ℕ∞) + ringKrullDim (A ⧸ q) = ringKrullDim A := by
    rw [hquot, DivisorClass.Chern.IntegralDimension.Construction.integral_ringKrullDim_eq (R := P) (S := A) hinj]
    change (p : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin n) K ⧸ r) = _
    have h := OAI.Algebra.Foundations.PolynomialCatenaryT.PolynomialCatenary.MvPolynomial.height_add_ringKrullDim_quotient_eq_fin r
    rw [hr] at h
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      zero_add, ENat.card_eq_coe_fintype_card, Fintype.card_fin, WithBot.coe_natCast]
    simpa only [WithBot.coe_natCast] using h
  rw [DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K (A ⧸ q), DivisorClass.Chern.FiniteTypeDimension.Construction.finiteType_ringKrullDim_eq_trdeg K A] at hdim
  have h : p + (Algebra.trdeg K (A ⧸ q)).toNat = (Algebra.trdeg K A).toNat := by
    exact_mod_cast hdim
  omega

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual reduced closure of a codimension-`p` point has dimension `dim X - p`. -/
theorem pointClosure_dimension_add_coheight {X : Scheme} [IsIntegral X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (x : X)
    (p : ℕ) (hx : Order.coheight x = p) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + p =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let V : X.affineOpens := ⟨U, hU⟩
  let Z : IrreducibleCloseds X := irreducibleSetEquivPoints.symm x
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Nonempty (Foundations.Scheme.SupportAffineQuotient.supportAffineOpen Z V) := (Foundations.Scheme.SupportAffineInclusion.supportAffineOpen_nonempty_iff Z V).mpr
    ⟨x, subset_closure (Set.mem_singleton x), hxU⟩
  let : Algebra ℂ Γ(X, U) := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let : Algebra.FiniteType ℂ Γ(X, U) := Foundations.Scheme.AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U hU
  let : ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal V).IsPrime := Foundations.Scheme.SupportAffineQuotient.supportAffineIdeal_isPrime Z V
  have hp : ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal V).height = p :=
    (DivisorClass.Chern.SupportCodimension.Construction.pointClosure_affineIdeal_height x V hxU).trans hx
  rw [Foundations.Scheme.SupportDimension.supportTranscendenceDimension_eq_affineQuotient Z f V,
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_affineSections f U hU]
  exact finiteType_height_trdeg ℂ Γ(X, U) ((CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal V) p hp

/-- Both cycle constructions assign the same codimension to the same actual reduced support. -/
theorem originalPoint_dimensionCodimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x : V.carrier) (p : ℕ) (hx : Order.coheight x = p) :
    CycleClass.Geometric.DimensionCycles.dimensionCodimension V (irreducibleSetEquivPoints.symm x) = p := by
  have h := pointClosure_dimension_add_coheight V.structureMap x p hx
  dsimp [CycleClass.Geometric.DimensionCycles.dimensionCodimension]
  omega

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleCodimension
