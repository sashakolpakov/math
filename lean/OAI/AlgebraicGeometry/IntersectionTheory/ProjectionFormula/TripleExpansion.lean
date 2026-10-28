import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricIteratedExpansion
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TripleSupportEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicPrincipalDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.StalkPrime

/-! # Triple Expansion -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TripleExpansion

noncomputable section

/-! The local iterated Euler pairing expands into products of the
native intersection multiplicities of the intermediate supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem quotient_euler (Z : Scheme) (B : IrreducibleCloseds Z) (x : Z)
    (hxB : x ∈ (B : Set Z)) (p : PrimeSpectrum (Z.presheaf.stalk x)) (d : ℕ) :
    Tor.Euler.euler (Z.presheaf.stalk x) (.of _ (Z.presheaf.stalk x ⧸ p.asIdeal))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) d =
    TotalTorCoefficient.coefficient Z (Stalk.DivisorSupport.primeClosure Z x p) B x d := by
  let e := (Stalk.PrimeQuotient.moduleEquiv Z (Stalk.DivisorSupport.primeClosure Z x p) x
    (Stalk.DivisorSupport.point_mem_primeClosure Z x p) p (Stalk.DivisorSupport.primeClosure_point Z x p).symm).toModuleIso
  rw [← PrimeFiltrationEuler.euler_iso_left (Z.presheaf.stalk x) e (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB) d,
    TotalTorCoefficient.coefficient, dite_eq_left ⟨Stalk.DivisorSupport.point_mem_primeClosure Z x p, hxB⟩]
  rfl

theorem exists_sum (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q t : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) (D : X.DimensionCycleSupport t)
    (hpair : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ (A.val : Set X.carrier) ∩ B.val → p + q ≤ X.supportCodimension E)
    (htriple : ∀ E : IrreducibleCloseds X.carrier,
      (E : Set X.carrier) ⊆ ((A.val : Set X.carrier) ∩ B.val) ∩ D.val → p + q + t ≤ X.supportCodimension E)
    (C : X.DimensionCycleSupport (p + q + t))
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (B.val : Set X.carrier))
    (hxD : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (D.val : Set X.carrier)) :
    ∃ F : Finset (PrimeSpectrum (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))),
      (∀ v ∈ F, X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) v) = p + q ∧
        Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) v ≤ A.val ∧
        Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) v ≤ B.val) ∧
      (∀ v, X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) v) = p + q → v ∉ F →
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) v) = 0) ∧
      IteratedTorEuler.euler (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier D.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxD)
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxB)
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA) m m =
      ∑ v ∈ F, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) v) *
        CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) v) D.val C.val := by
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let R := X.carrier.presheaf.stalk x
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A.val x hxA
  let M := CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B.val x hxB
  let L := CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier D.val x hxD
  let : Module.Finite R N := Local.TorFinite.localSupportModule_finite _ _ _ _
  let : Module.Finite R M := Local.TorFinite.localSupportModule_finite _ _ _ _
  let : Module.Finite R L := Local.TorFinite.localSupportModule_finite _ _ _ _
  have hc := Grading.supportDimension_add_codimension X m C.val
  have hd := Grading.supportDimension_add_codimension X m D.val
  rw [C.property] at hc
  rw [D.property] at hd
  have hNM : ∀ v ∈ Module.support R N ∩ Module.support R M,
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X.carrier x v) X.structureMap ≤ m - (p + q) := by
    intro v hv
    have ha := IntrinsicPrincipalDimension.Intrinsic.support_le X.carrier A.val x hxA v hv.1
    have hb := IntrinsicPrincipalDimension.Intrinsic.support_le X.carrier B.val x hxB v hv.2
    have hp := hpair (Stalk.DivisorSupport.primeClosure X.carrier x v) (Set.subset_inter ha hb)
    have he := Grading.supportDimension_add_codimension X m (Stalk.DivisorSupport.primeClosure X.carrier x v)
    omega
  have hL : ∀ v ∈ Module.support R L,
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Stalk.DivisorSupport.primeClosure X.carrier x v) X.structureMap ≤
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension D.val X.structureMap := by
    intro v hv
    exact (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono X.structureMap).monotone
      (IntrinsicPrincipalDimension.Intrinsic.support_le X.carrier D.val x hxD v hv)
  have heq : (m - (p + q)) + Foundations.Scheme.SupportDimension.supportTranscendenceDimension D.val X.structureMap =
      m + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) X.structureMap := by
    change _ = m + Foundations.Scheme.SupportDimension.supportTranscendenceDimension
      (irreducibleSetEquivPoints.symm (irreducibleSetEquivPoints C.val)) X.structureMap
    rw [irreducibleSetEquivPoints.symm_apply_apply]
    omega
  obtain ⟨F, hF, hout, he⟩ := GeometricIteratedExpansion.exists_sum X.structureMap m x N M L
    (m - (p + q)) (Foundations.Scheme.SupportDimension.supportTranscendenceDimension D.val X.structureMap) hNM hL heq
    (TripleSupportEuler.isolated X m (p + q + t) A.val B.val D.val htriple C hxA hxB hxD)
  have hfirst (v : PrimeSpectrum R) :
      Tor.Euler.euler (Localization.AtPrime v.asIdeal)
        ((Flat.Extension.baseChange R (Localization.AtPrime v.asIdeal)).obj N)
        ((Flat.Extension.baseChange R (Localization.AtPrime v.asIdeal)).obj M) m =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val (Stalk.DivisorSupport.primeClosure X.carrier x v) := by
    rw [← TotalTorCoefficient.localization X.carrier A.val B.val x hxA hxB v m,
      ← Stalk.DivisorSupport.primeClosure_point]
    exact Closed.StalkPrime.projective_coefficient X m A.val B.val (Stalk.DivisorSupport.primeClosure X.carrier x v) m le_rfl
  have hsecond (v : PrimeSpectrum R) : Tor.Euler.euler R (.of R (R ⧸ v.asIdeal)) L m =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier x v) D.val C.val := by
    rw [quotient_euler X.carrier D.val x hxD v m]
    exact Closed.StalkPrime.projective_coefficient X m (Stalk.DivisorSupport.primeClosure X.carrier x v) D.val C.val m le_rfl
  refine ⟨F, ?_, ?_, ?_⟩
  · intro v hv
    have hf := hF v hv
    have he := Grading.supportDimension_add_codimension X m (Stalk.DivisorSupport.primeClosure X.carrier x v)
    have hvdim : X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier x v) = p + q := by omega
    refine ⟨hvdim, IntrinsicPrincipalDimension.Intrinsic.support_le X.carrier A.val x hxA v hf.1.1,
      IntrinsicPrincipalDimension.Intrinsic.support_le X.carrier B.val x hxB v hf.1.2⟩
  · intro v hv hvF
    change X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier x v) = p + q at hv
    rw [← hfirst v]
    apply hout v _ hvF
    have he := Grading.supportDimension_add_codimension X m (Stalk.DivisorSupport.primeClosure X.carrier x v)
    omega
  · rw [IsolatedIteratedTorEuler.euler_eq_sum, he]
    apply Finset.sum_congr rfl
    intro v _
    rw [hfirst, hsecond]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TripleExpansion
