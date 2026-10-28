import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.BallAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArchimedeanCompactness
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.DefiniteEmbeddings
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.LatticeTorsion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProperActionTransport
import OAI.Geometry.ComplexBall.Free
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.Covering.Quotient

/-! # Ball Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.BallQuotient.HermitianBall

noncomputable section

/-! The literal principal subgroup of an arbitrary normalized Hermitian
lattice acts on the prescribed ball. Its exact orbit quotient is compact,
and at level at least three the original orbit projection is a covering. -/

open _root_.NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)
    (H : Matrix (Fin 3) (Fin 3) E)
    (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (he : ∀ x y, Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (N : ℕ)

local notation "Γ" => (OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup (R := E) Λ.toAddSubgroup N ⊓
  Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H) :
    Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))

theorem principalAction_continuousConstSMul :
    letI := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
    ContinuousConstSMul Γ P.Domain := by
  let := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
  constructor
  intro g
  change Continuous (fun z : P.Domain => P.arithmeticBallEquiv.symm
    (BallAction.HermitianBall.principalHom P H e he δ hδ hδ0 Λ N g • P.arithmeticBallEquiv z))
  exact P.arithmeticBallEquiv.symm.continuous.comp
    ((continuous_const_smul (BallAction.HermitianBall.principalHom P H e he δ hδ hδ0 Λ N g)).comp
      P.arithmeticBallEquiv.continuous)

def orbitSetoid : Setoid P.Domain :=
  letI := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
  MulAction.orbitRel Γ P.Domain

theorem orbitSetoid_iff (z w : P.Domain) :
    (orbitSetoid P H e he δ hδ hδ0 Λ N).r z w ↔
      ∃ g ∈ (Groups.principalLatticeSubgroup (R := E) Λ.toAddSubgroup N ⊓
        Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)),
        w.val = P.lineActionVia e g z.val := by
  let := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
  change (∃ a : Γ, a • w = z) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    have hw : w = a⁻¹ • z := by rw [← ha, inv_smul_smul]
    exact ⟨a⁻¹, (a⁻¹).property, (congrArg Subtype.val hw).trans
      (BallAction.HermitianBall.principalAction_val P H e he δ hδ hδ0 Λ N a⁻¹ z)⟩
  · rintro ⟨a, ha, hw⟩
    let b : Γ := ⟨a, ha⟩
    have hb : w = b • z := Subtype.ext (hw.trans
      (BallAction.HermitianBall.principalAction_val P H e he δ hδ hδ0 Λ N b z).symm)
    exact ⟨b⁻¹, (congrArg (fun q : P.Domain => b⁻¹ • q) hb).trans (inv_smul_smul b z)⟩

def orbitProjection : P.Domain → Quotient (orbitSetoid P H e he δ hδ hδ0 Λ N) := Quotient.mk _

theorem orbitProjection_fibers (z w : P.Domain) :
    orbitProjection P H e he δ hδ hδ0 Λ N z = orbitProjection P H e he δ hδ hδ0 Λ N w ↔
      ∃ g ∈ (Groups.principalLatticeSubgroup (R := E) Λ.toAddSubgroup N ⊓
        Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H)),
        w.val = P.lineActionVia e g z.val :=
  Quotient.eq.trans (orbitSetoid_iff P H e he δ hδ hδ0 Λ N z w)

theorem orbitProjection_continuous : Continuous (orbitProjection P H e he δ hδ hδ0 Λ N) :=
  continuous_quotient_mk'

theorem orbitProjection_surjective : Function.Surjective (orbitProjection P H e he δ hδ hδ0 Λ N) :=
  Quotient.mk_surjective

theorem orbitProjection_isOpenQuotientMap :
    IsOpenQuotientMap (orbitProjection P H e he δ hδ hδ0 Λ N) := by
  let := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
  let : ContinuousConstSMul Γ P.Domain := principalAction_continuousConstSMul P H e he δ hδ hδ0 Λ N
  exact MulAction.isOpenQuotientMap_quotientMk

theorem orbitQuotient_secondCountable :
    SecondCountableTopology (Quotient (orbitSetoid P H e he δ hδ hδ0 Λ N)) := by
  let := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
  let : ContinuousConstSMul Γ P.Domain := principalAction_continuousConstSMul P H e he δ hδ hδ0 Λ N
  exact ContinuousConstSMul.secondCountableTopology

def principalImage : Subgroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.ArchimedeanSU P.b P.μ) :=
  (BallAction.HermitianBall.principalHom P H e he δ hδ hδ0 Λ N).range

def principalImageEquiv : Γ ≃* principalImage P H e he δ hδ hδ0 Λ N :=
  MonoidHom.ofInjective (BallAction.HermitianBall.principalHom_injective P H e he δ hδ hδ0 Λ N)

theorem principalImageEquiv_action (g : Γ) (z : P.Domain) :
    letI := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
    P.arithmeticBallEquiv (g • z) =
      principalImageEquiv P H e he δ hδ hδ0 Λ N g • P.arithmeticBallEquiv z :=
  BallAction.HermitianBall.principalAction_equivariant P H e he δ hδ hδ0 Λ N g z

theorem orbit_arithmetic_iff (z w : P.Domain) :
    (orbitSetoid P H e he δ hδ hδ0 Λ N).r z w ↔
      MulAction.orbitRel (principalImage P H e he δ hδ hδ0 Λ N) (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (P.μ P.b))
        (P.arithmeticBallEquiv z) (P.arithmeticBallEquiv w) := by
  let := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
  change (∃ g : Γ, g • w = z) ↔
    ∃ g : principalImage P H e he δ hδ hδ0 Λ N,
      g • P.arithmeticBallEquiv w = P.arithmeticBallEquiv z
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨principalImageEquiv P H e he δ hδ hδ0 Λ N g,
      (principalImageEquiv_action P H e he δ hδ hδ0 Λ N g w).symm.trans
        (congrArg P.arithmeticBallEquiv hg)⟩
  · rintro ⟨g, hg⟩
    obtain ⟨g, rfl⟩ := (principalImageEquiv P H e he δ hδ hδ0 Λ N).surjective g
    exact ⟨g, P.arithmeticBallEquiv.injective
      ((principalImageEquiv_action P H e he δ hδ hδ0 Λ N g w).trans hg)⟩

def orbitHomeomorph : Quotient (orbitSetoid P H e he δ hδ hδ0 Λ N) ≃ₜ
    MulAction.orbitRel.Quotient (principalImage P H e he δ hδ hδ0 Λ N) (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (P.μ P.b)) :=
  Homeomorph.Quotient.congr P.arithmeticBallEquiv (orbit_arithmetic_iff P H e he δ hδ hδ0 Λ N)

theorem orbitHomeomorph_projection (z : P.Domain) :
    orbitHomeomorph P H e he δ hδ hδ0 Λ N (orbitProjection P H e he δ hδ hδ0 Λ N z) =
      Quotient.mk (MulAction.orbitRel (principalImage P H e he δ hδ hδ0 Λ N)
        (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (P.μ P.b))) (P.arithmeticBallEquiv z) := rfl

theorem principalImage_eq_map :
    principalImage P H e he δ hδ hδ0 Λ N =
      (ArchimedeanCompactness.HermitianArithmetic.principalComplexHom δ hδ hδ0 H P.μ Λ N).range.map
        (BallAction.HermitianBall.normalizedEquiv P H e he).toMonoidHom := by
  rw [MonoidHom.map_range]
  rfl

variable (hP : P.IsAdmissible)
    (hH : ∀ i j, H i j = IsCMField.complexConj E (H j i)) (hdet : H.det ≠ 0)
    (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (han : ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Datum.RankThreePELDatum.matrixHermitian H v v = 0 → v = 0)
    (hdef : ∀ i, i ≠ P.distinguished →
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        0 < (Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        (Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom H x x).re < 0))

include hH hdet hΛ han in
theorem principalImage_cosets_compact (hN : N ≠ 0) :
    CompactSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.ArchimedeanSU P.b P.μ ⧸ principalImage P H e he δ hδ hδ0 Λ N) := by
  let : CompactSpace (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map P.μ) ⧸
      (ArchimedeanCompactness.HermitianArithmetic.principalComplexHom δ hδ hδ0 H P.μ Λ N).range) :=
    ArchimedeanCompactness.HermitianArithmetic.principal_complex_compact δ hδ hδ0 H P.μ hH hdet han Λ hΛ N hN
  rw [principalImage_eq_map]
  exact NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure.Construction.compact_quotient_map_of_surjective (BallAction.HermitianBall.normalizedEquiv P H e he).toMonoidHom
    (BallAction.HermitianBall.normalizedEquiv P H e he).continuous (BallAction.HermitianBall.normalizedEquiv P H e he).surjective _

include hP hH hdet hΛ hdef in
theorem principalImage_discrete (hN : N ≠ 0) :
    DiscreteTopology (principalImage P H e he δ hδ hδ0 Λ N) := by
  let : DiscreteTopology (ArchimedeanCompactness.HermitianArithmetic.principalComplexHom δ hδ hδ0 H P.μ Λ N).range :=
    ArchimedeanCompactness.HermitianArithmetic.principal_complex_discrete δ hδ hδ0 H P.μ hH hdet
      (P.definite_other_embedding hP H hdef) Λ hΛ N hN
  rw [principalImage_eq_map]
  exact NumberTheory.ArithmeticGroups.Lattices.Discrete.Construction.discrete_map_of_closedMap (BallAction.HermitianBall.normalizedEquiv P H e he).toMonoidHom
    (BallAction.HermitianBall.normalizedEquiv P H e he).toHomeomorph.isClosedMap _

include hP hH hdet hΛ han in
theorem orbitQuotient_compact (hN : N ≠ 0) :
    CompactSpace (Quotient (orbitSetoid P H e he δ hδ hδ0 Λ N)) := by
  let : CompactSpace (Geometry.ComplexBall.ArithmeticQuotientEquationsData.ArchimedeanSU P.b P.μ ⧸ principalImage P H e he δ hδ hδ0 Λ N) :=
    principalImage_cosets_compact P H e he δ hδ hδ0 Λ N hH hdet hΛ han hN
  have him : (P.μ P.b).im = 0 := by
    have h := congrArg P.μ hP.2.1
    rw [IsCMField.complexEmbedding_complexConj] at h
    exact Complex.conj_eq_iff_im.mp h
  let : CompactSpace (MulAction.orbitRel.Quotient
      (principalImage P H e he δ hδ hδ0 Λ N) (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (P.μ P.b))) :=
    Geometry.ComplexBall.QuotientCompact.Arithmetic.ballQuotient_compact _ him hP.2.2.2.1 _
  exact (orbitHomeomorph P H e he δ hδ hδ0 Λ N).symm.compactSpace

local instance : LocallyCompactSpace P.Domain := P.domainOpen.isOpen.locallyCompactSpace

include hP hH hdet hΛ hdef in
theorem principalAction_properlyDiscontinuous (hN : N ≠ 0) :
    letI := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
    ProperlyDiscontinuousSMul Γ P.Domain := by
  let := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
  let : DiscreteTopology (principalImage P H e he δ hδ hδ0 Λ N) :=
    principalImage_discrete P H e he δ hδ hδ0 Λ N hP hH hdet hΛ hdef hN
  have him : (P.μ P.b).im = 0 := by
    have h := congrArg P.μ hP.2.1
    rw [IsCMField.complexEmbedding_complexConj] at h
    exact Complex.conj_eq_iff_im.mp h
  let : ProperlyDiscontinuousSMul (principalImage P H e he δ hδ hδ0 Λ N)
      (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (P.μ P.b)) :=
    Geometry.ComplexBall.ArithmeticQuotientBoostBall.discrete_ballAction_properlyDiscontinuous _ him hP.2.2.2.1 _
  exact ProperActionTransport.properlyDiscontinuous_of_equivariant_injection
    (principalImageEquiv P H e he δ hδ hδ0 Λ N)
    (principalImageEquiv P H e he δ hδ hδ0 Λ N).injective P.arithmeticBallEquiv
    (principalImageEquiv_action P H e he δ hδ hδ0 Λ N)

include hP hH hdet hΛ hdef in
theorem principalAction_free (hN : 3 ≤ N) :
    letI := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
    IsCancelSMul Γ P.Domain := by
  let := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
  let : ProperlyDiscontinuousSMul Γ P.Domain :=
    principalAction_properlyDiscontinuous P H e he δ hδ hδ0 Λ N hP hH hdet hΛ hdef (by omega)
  have hspan : Submodule.span E (Λ : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤ := by
    have hle : Submodule.span ℚ (Λ : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) ≤
        (Submodule.span E (Λ : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))).restrictScalars ℚ :=
      Submodule.span_le.mpr (fun _ hx => Submodule.subset_span hx)
    rw [hΛ.2.1] at hle
    exact top_unique hle
  apply Geometry.ComplexBall.Free.ArithmeticQuotient.free_of_properlyDiscontinuous_torsionFree
  intro g k hk hp
  exact Subtype.ext (Principal.LatticeTorsion.principalLattice_torsion_free Λ hΛ.1 hspan N hN g.val g.property.1
    k hk (congrArg Subtype.val hp))

include hP hH hdet hΛ hdef in
theorem orbitProjection_covering (hN : 3 ≤ N) :
    IsCoveringMap (orbitProjection P H e he δ hδ hδ0 Λ N) := by
  let := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
  let : ContinuousConstSMul Γ P.Domain := principalAction_continuousConstSMul P H e he δ hδ hδ0 Λ N
  let : ProperlyDiscontinuousSMul Γ P.Domain :=
    principalAction_properlyDiscontinuous P H e he δ hδ hδ0 Λ N hP hH hdet hΛ hdef (by omega)
  let : IsCancelSMul Γ P.Domain :=
    principalAction_free P H e he δ hδ hδ0 Λ N hP hH hdet hΛ hdef hN
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap

include hP hH hdet hΛ hdef in
theorem orbitQuotient_hausdorff (hN : N ≠ 0) :
    T2Space (Quotient (orbitSetoid P H e he δ hδ hδ0 Λ N)) := by
  let := BallAction.HermitianBall.principalAction P H e he δ hδ hδ0 Λ N
  let : ContinuousConstSMul Γ P.Domain := principalAction_continuousConstSMul P H e he δ hδ hδ0 Λ N
  let : ProperlyDiscontinuousSMul Γ P.Domain :=
    principalAction_properlyDiscontinuous P H e he δ hδ hδ0 Λ N hP hH hdet hΛ hdef hN
  exact inferInstanceAs (T2Space (MulAction.orbitRel.Quotient Γ P.Domain))

include hP in
theorem orbitQuotient_connected : ConnectedSpace (Quotient (orbitSetoid P H e he δ hδ hδ0 Λ N)) := by
  let : ConnectedSpace P.Domain := P.domain_connected hP
  exact (orbitProjection_surjective P H e he δ hδ hδ0 Λ N).connectedSpace
    (orbitProjection_continuous P H e he δ hδ hδ0 Λ N)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.BallQuotient.HermitianBall
