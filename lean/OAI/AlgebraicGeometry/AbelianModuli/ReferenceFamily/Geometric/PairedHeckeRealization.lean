import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HeckeEtale
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairedKernelModule
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELPolarization

/-! # Paired Hecke Realization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairedHeckeRealization

noncomputable section

/-! Every actual paired quotient at a geometric point lies on one of
the constructed finite etale correspondences. Its own finite kernel
supplies the module type, and both original moduli points are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FinePELPolarization.Construction

theorem geometric_pair_realized_by_finite_etale_hecke
    {E K k : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    [Field k] [IsAlgClosed k]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (Z : Models.FinePELModel P iota N) (hZ : Z.IsFine)
    [IsLocallyNoetherian Z.space.left] [LocallyOfFiniteType Z.space.hom]
    (hN : 3 ≤ N) (hn : 0 < n) (hcop : Nat.Coprime n N) (hmod : Nat.ModEq N n 1)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    {b : Spec (.of k) ⟶ Spec (.of K)}
    {A B : PEL.Objects.PELObject P iota N (Over.mk b)} (f : Paired.PELQuotients.PairedPELQuotient A B n) :
    ∃ R : NoetherianPairedHeckeSource.PairedHeckeSource Z.universal n hn f.geometricKernelModule,
      IsFinite (R.targetProjection Z hZ).left ∧ Etale (R.targetProjection Z hZ).left ∧
      ∃ u : Over.mk b ⟶ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter,
        Nonempty (Paired.PELFunctor.PairedPELQuotientIso (R.quotient.pullback u) f) ∧
        u ≫ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space R.parameter = AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap Z hZ A ∧
        u ≫ R.targetProjection Z hZ = AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap Z hZ B := by
  let M := f.geometricKernelModule
  obtain ⟨R, hfin, het, _, _⟩ := HeckeEtale.exists_finite_etale_paired_hecke_correspondence
    Z hZ hN n hn hcop hmod hdegree M
  let F : Paired.PELFunctor.PairedPELObject P iota N n (Over.mk b) := ⟨A, B, f⟩
  let u := Paired.HeckeObjectClassifier.pairedHeckeObjectClassifyingMap Z hZ hdegree M R F f.geometricKernelModule_type
  let e := HeckePairClassSurjectivity.pairedHeckeObjectRecoveryIso Z hZ hdegree M R F f.geometricKernelModule_type
  refine ⟨R, hfin, het, u, ⟨e⟩,
    Paired.HeckeObjectClassifier.pairedHeckeObjectClassifyingMap_source Z hZ hdegree M R F f.geometricKernelModule_type, ?_⟩
  have ht := AbelianScheme.IsogenyQuotient.FinePELPolarization.Construction.finePELClassifyingMap_eq_of_iso Z hZ e.target
  rw [AbelianScheme.IsogenyQuotient.FinePELPolarization.Construction.finePELClassifyingMap_pullback] at ht
  exact ht

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairedHeckeRealization
