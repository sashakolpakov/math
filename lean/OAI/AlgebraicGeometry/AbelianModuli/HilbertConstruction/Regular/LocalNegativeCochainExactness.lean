import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.LocalCochainAcyclicity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.ComplexExtension

/-! # Local Negative Cochain Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.LocalNegativeCochainExactness

noncomputable section

/-! A finite free complex beginning in degree -g over a regular local
ring of dimension g is exact in every negative degree when its field
fibers away from the closed point are acyclic. The proof shifts the
actual complex to nonnegative degrees before applying local acyclicity. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u

theorem regularLocal_negative_cochain_exact
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (g : ℕ)
    (hfin : ∀ i, Module.Finite R (C.X i)) (hfree : ∀ i, Module.Free R (C.X i))
    (hbelow : ∀ i, i < -(g : ℤ) → IsZero (C.X i))
    (rs : List R) (hlen : rs.length = g) (hreg : SequenceBasic.RingTheory.Sequence.IsRegular R rs)
    (hgen : SequenceBasic.Ideal.ofList rs = maximalIdeal R)
    (hfield : ∀ (B : Type u) [Field B] [Algebra R B],
      ¬ maximalIdeal R ≤ RingHom.ker (algebraMap R B) →
      (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℤ)).obj C).Acyclic) :
    ∀ i, i < 0 → C.ExactAt i := by
  let e := ComplexShape.embeddingUpIntGE (-(g : ℤ))
  have hout (i : ℤ) (hi : ∀ n, e.f n ≠ i) : i < -(g : ℤ) := by
    by_contra h
    apply hi (i + g).toNat
    change -(g : ℤ) + ((i + g).toNat : ℤ) = i
    omega
  let : C.IsStrictlySupported e := { isZero := fun i hi => hbelow i (hout i hi) }
  let D := C.restriction e
  have hfieldD : Cochain.FieldSupport.CochainFieldSupport D (maximalIdeal R) := by
    intro B _ _ hnot
    let F := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B
    let CB := (F.mapHomologicalComplex (.up ℤ)).obj C
    let : CB.IsStrictlySupported e := {
      isZero := fun i hi => F.map_isZero (hbelow i (hout i hi)) }
    have hD : ((F.mapHomologicalComplex (.up ℕ)).obj D).Acyclic := by
      change (CB.restriction e).Acyclic
      exact Additive.ComplexExtension.supported_restriction_acyclic e CB (hfield B hnot)
    intro q
    exact (Base.ChangeTensorExactness.baseChange_exactAt_iff_tensor D q).mp (hD q)
  have hz := LocalCochainAcyclicity.regularLocalCochain_homology_zero_below_regular_parameters g R D
    (fun q => hfin (e.f q)) (fun q => hfree (e.f q)) rs hlen hreg hgen hfieldD
  intro i hi
  by_cases hib : i < -(g : ℤ)
  · exact HomologicalComplex.ExactAt.of_isZero (hbelow i hib)
  · let q := (i + g).toNat
    have hqi : e.f q = i := by
      change -(g : ℤ) + ((i + g).toNat : ℤ) = i
      omega
    have hqg : q < g := by dsimp [q]; omega
    have hD : D.ExactAt q := (D.exactAt_iff_isZero_homology q).mpr (hz q hqg)
    have hC := (Additive.ComplexExtension.supported_restriction_exactAt_iff e C q).mp hD
    simpa only [hqi] using hC

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.LocalNegativeCochainExactness
