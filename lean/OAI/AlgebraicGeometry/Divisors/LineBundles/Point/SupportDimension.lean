import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecializationGrading
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension

/-! # Support Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension.BundleCycles

noncomputable section

/-!
# LineBundleCycles: point-support dimension under closed immersion

On a common affine chart, a closed immersion induces a surjection of
coordinate rings. Quotienting by the actual point primes therefore gives
isomorphic algebras and preserves the transcendence dimension of the
reduced point closures.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {k : Type} [Field k] {X Y : Scheme}

/-- The point closure has the dimension of its actual affine prime quotient. -/
theorem pointClosure_dimension_eq_affine (f : X ⟶ Spec (CommRingCat.of k))
    (x : X) (U : X.affineOpens) (hx : x ∈ U.1) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U.1
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f =
      (Algebra.trdeg k (Γ(X, U.1) ⧸ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)).toNat := by
  let Z := irreducibleSetEquivPoints.symm x
  have : Nonempty (Foundations.Scheme.SupportAffineQuotient.supportAffineOpen Z U) :=
    (Foundations.Scheme.SupportAffineInclusion.supportAffineOpen_nonempty_iff Z U).mpr ⟨x, subset_closure (Set.mem_singleton x), hx⟩
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U.1
  have h := Foundations.Scheme.SupportDimension.supportTranscendenceDimension_eq_affineQuotient Z f U
  exact h.trans (congrArg (fun J : Ideal Γ(X, U.1) => (Algebra.trdeg k (Γ(X, U.1) ⧸ J)).toNat)
    (DivisorClass.Chern.SupportCodimension.Construction.pointClosure_affineIdeal x U hx))

/-- A closed immersion preserves the dimension of every reduced point closure. -/
theorem pointClosure_dimension_closedImmersion (i : X ⟶ Y) [IsClosedImmersion i]
    (f : Y ⟶ Spec (CommRingCat.of k)) (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i x)) f =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (i x))
  let V := i ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage i
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (i ≫ f) V
  let p := hU.primeIdealOf ⟨i x, hxU⟩
  let q := hV.primeIdealOf ⟨x, hxU⟩
  let a := Foundations.Scheme.ClosedImmersionDimension.sectionPullbackAlgHom i f U
  have hprime : q.asIdeal.comap a.toRingHom = p.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hxU
    have he := congrArg PrimeSpectrum.asIdeal h
    change q.asIdeal.comap (i.appLE U V le_rfl).hom = p.asIdeal at he
    exact (congrArg (fun b : Γ(Y, U) ⟶ Γ(X, V) => q.asIdeal.comap b.hom)
      i.app_eq_appLE).trans he
  have hq := Affine.SpecializationGrading.BundleCycles.quotient_trdeg_of_surjective (k := k) (A := Γ(Y, U)) (B := Γ(X, V))
    a (Foundations.Scheme.ClosedImmersionDimension.sectionPullbackAlgHom_surjective i f U hU) q.asIdeal
  have hpDim : (Algebra.trdeg k (Γ(Y, U) ⧸ p.asIdeal)).toNat =
      (Algebra.trdeg k (Γ(X, V) ⧸ q.asIdeal)).toNat :=
    (congrArg (fun J : Ideal Γ(Y, U) => (Algebra.trdeg k (Γ(Y, U) ⧸ J)).toNat) hprime.symm).trans
      (congrArg Cardinal.toNat hq)
  exact (pointClosure_dimension_eq_affine f (i x) ⟨U, hU⟩ hxU).trans
    (hpDim.trans (pointClosure_dimension_eq_affine (i ≫ f) x ⟨V, hV⟩ hxU).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension.BundleCycles
