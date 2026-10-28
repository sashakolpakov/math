import OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Components
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Models -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Models

noncomputable section

section

/-!
Concrete arithmetic PEL families for CMPoints. A finite collection may have
different moduli bases; all are defined over the same arithmetic base.
Each geometric fiber and its abelian family is constructed by pullback.
The supplied integral models are exactly the objects produced by IntegralModel.
CM points, ordinarity, torsion heights and duality are not model fields.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

/-- The geometric point above x, exactly as in Openness. -/
def geometricPoint (S : Scheme) (x : S) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap (S.residueField x) (AlgebraicClosure (S.residueField x)))) ≫
      S.fromSpecResidueField x)

/-- The source's ordinary condition, including the actual fiber dimension. -/
def IsOrdinaryAt (q : ℕ) {S : Scheme} (A : Over S) [GrpObj A] (x : S) : Prop :=
  ∃ g : ℕ,
    topologicalKrullDim (A.hom.fiber x) = (g : WithBot ℕ∞) ∧
    Nat.card {z : geometricPoint S x ⟶ A // z ^ q = 1} = q ^ g

variable (E K : Type) [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [IsGalois ℚ E] [Field K] [NumberField K]

/-- A finite collection of the actual integral universal families of IntegralModel.
All geometric and moduli conditions are in the separate predicate below. -/
structure RankThreePELModel where
  s : ℕ
  familyCount : ℕ
  iota : E →+* K
  complexEmbedding : K →+* ℂ
  arithmetic : IntegralModel.Base.ArithmeticBaseExtension K complexEmbedding
  datum : Fin familyCount → AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s
  level : Fin familyCount → ℕ
  moduli : ∀ a, AbelianModuli.ReferenceFamily.Models.FinePELModel (datum a) iota (level a)
  integral : ∀ a, IntegralModel.PEL.Has.IntegralPELSpread (datum a) iota complexEmbedding
    (level a) (moduli a).space (moduli a).universal arithmetic
  componentCount : Fin familyCount → ℕ
  components : ∀ a, IntegralModel.Components.ComponentAlbaneseData (integral a).toOver (componentCount a)
  decomposition : ∀ a, (∐ (components a).S) ≅ (integral a).toOver

namespace RankThreePELModel

variable {E K} (M : RankThreePELModel E K)

abbrev Family := Fin M.familyCount

/-- The prior complex period and integral-model conditions. In particular
there is no ordinary point or ordinary-locus condition here. -/
def HasPrescribedBallPeriods : Prop :=
  0 < M.s ∧ Module.finrank ℚ E = 2 * M.s ∧
  ∀ a : M.Family,
    (M.datum a).IsAdmissible ∧
    M.complexEmbedding.comp M.iota = (M.datum a).μ ∧
    IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel (M.datum a) (M.level a) ∧
    (M.moduli a).IsFine ∧
    (M.moduli a).HasProjectiveBallComponents M.complexEmbedding ∧
    IntegralModel.PEL.Has.IntegralPELSpread.IsReducedPELModuli (M.datum a) (M.integral a) ∧
    Smooth (M.integral a).toOver.hom ∧
    IsProper (M.integral a).toOver.hom ∧
    IntegralModel.Components.RelativelyProjective (M.integral a).toOver ∧
    ∀ t : Fin (M.componentCount a),
      Smooth ((M.components a).S t).hom ∧
      IsProper ((M.components a).S t).hom ∧
      IntegralModel.Components.RelativelyProjective ((M.components a).S t) ∧
      GeometricallyConnected ((M.components a).S t).hom

/-- Direct adapter for one of IntegralModel's integral universal families. The
adapter contains only the actual objects in IntegralModel's conclusion. -/
def ofSingleIntegralFamily
    {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iota : E →+* K) (κ : K →+* ℂ)
    (F : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ)
    (T : IntegralModel.PEL.Has.IntegralPELSpread P iota κ N F.space F.universal B)
    (r : ℕ) (D : IntegralModel.Components.ComponentAlbaneseData T.toOver r)
    (e : (∐ D.S) ≅ T.toOver) : RankThreePELModel E K where
  s := s
  familyCount := 1
  iota := iota
  complexEmbedding := κ
  arithmetic := B
  datum _ := P
  level _ := N
  moduli _ := F
  integral _ := T
  componentCount _ := r
  components _ := D
  decomposition _ := e

omit [IsGalois ℚ E] in
/-- IntegralModel's geometric clauses and the prior ball description give exactly
the repaired model predicate; no ordinary-specialization premise is added. -/
theorem ofSingleIntegralFamily_hasPeriods
    {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iota : E →+* K) (κ : K →+* ℂ)
    (F : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ)
    (T : IntegralModel.PEL.Has.IntegralPELSpread P iota κ N F.space F.universal B)
    (r : ℕ) (D : IntegralModel.Components.ComponentAlbaneseData T.toOver r)
    (e : (∐ D.S) ≅ T.toOver)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hP : P.IsAdmissible) (hiota : κ.comp iota = P.μ)
    (hN : IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N)
    (hF : F.IsFine) (hball : F.HasProjectiveBallComponents κ)
    (hT : IntegralModel.PEL.Has.IntegralPELSpread.IsReducedPELModuli P T ∧
      Smooth T.toOver.hom ∧ IsProper T.toOver.hom ∧ IntegralModel.Components.RelativelyProjective T.toOver)
    (hD : ∀ t : Fin r,
      Smooth (D.S t).hom ∧ IsProper (D.S t).hom ∧
      IntegralModel.Components.RelativelyProjective (D.S t) ∧ GeometricallyConnected (D.S t).hom) :
    (ofSingleIntegralFamily P iota κ F B T r D e).HasPrescribedBallPeriods := by
  exact ⟨hs, hdegree, fun _ =>
    ⟨hP, hiota, hN, hF, hball, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2, hD⟩⟩

abbrev QadicChoice (q : ℕ) [Fact q.Prime] :=
  Arithmetic.QadicChoice M.arithmetic.extension.carrier M.arithmetic.embedding q

def extendedEmbedding : E →+* M.arithmetic.extension.carrier :=
  (algebraMap K M.arithmetic.extension.carrier).comp M.iota

/-- A residue map for the literal localization of the ring of integers,
compatible with the chosen q-adic embedding. Goodness excludes the actual
level and polarization denominators. Existence is a conclusion of CMPoints. -/
structure GoodIntegralReduction (q : ℕ) [Fact q.Prime] (j : M.QadicChoice q) where
  residue : M.arithmetic.R →+* ZMod q
  residue_compatibility :
    residue.comp (algebraMap (NumberField.RingOfIntegers M.arithmetic.extension.carrier)
      M.arithmetic.R) = j.residue
  levelPrimeToQ : ∀ a : M.Family, Nat.Coprime q (M.level a)
  polarizationPrimeToQ : ∀ a : M.Family,
    Nat.Coprime q ((∏ i, (M.datum a).polarizationType i) ^ 2)

namespace GoodIntegralReduction

variable {M} {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
  (R : M.GoodIntegralReduction q j)

def specialBase : Spec (.of (ZMod q)) ⟶ M.arithmetic.base :=
  Spec.map (CommRingCat.ofHom R.residue)

def geometricBase : Spec (.of (AlgebraicClosure (ZMod q))) ⟶ M.arithmetic.base :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).comp R.residue))

def specialFiber (a : M.Family) : Over (Spec (.of (ZMod q))) :=
  (Over.pullback R.specialBase).obj (M.integral a).toOver

def geometricFiber (a : M.Family) : Over (Spec (.of (AlgebraicClosure (ZMod q)))) :=
  (Over.pullback R.geometricBase).obj (M.integral a).toOver

abbrev geom (a : M.Family) : Scheme := (R.geometricFiber a).left

def geometricFiberOverPrimeField (a : M.Family) : Over (Spec (.of (ZMod q))) :=
  Over.mk ((R.geometricFiber a).hom ≫ Spec.map (CommRingCat.ofHom
    (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))))

def projection (a : M.Family) : R.geom a ⟶ (M.integral a).toOver.left :=
  pullback.fst (M.integral a).toOver.hom R.geometricBase

def polarized (a : M.Family) :
    AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * M.s) (M.datum a).polarizationType
      (M.level a) (R.geom a) :=
  (M.integral a).universal.data.polarized.pullback (R.projection a)

abbrev abelian (a : M.Family) := (R.polarized a).abelian

def action (a : M.Family) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (R.abelian a) :=
  (M.integral a).universal.data.action.pullback (R.projection a)

abbrev fiberField (a : M.Family) (x : R.geom a) :=
  AlgebraicClosure ((R.geom a).residueField x)

/-- The actual geometric point above a scheme point. -/
def fiberMap (a : M.Family) (x : R.geom a) : Spec (.of (R.fiberField a x)) ⟶ R.geom a :=
  Spec.map (CommRingCat.ofHom
    (algebraMap ((R.geom a).residueField x) (R.fiberField a x))) ≫
      (R.geom a).fromSpecResidueField x

def fiberPolarized (a : M.Family) (x : R.geom a) :=
  (R.polarized a).pullback (R.fiberMap a x)

abbrev fiberAbelian (a : M.Family) (x : R.geom a) :=
  (R.fiberPolarized a x).abelian

def fiberAction (a : M.Family) (x : R.geom a) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (R.fiberAbelian a x) :=
  (R.action a).pullback (R.fiberMap a x)

/-- The scalar map comes from the geometric fiber's structure morphism. -/
def fiberScalar (a : M.Family) (x : R.geom a) : ZMod q →+* R.fiberField a x :=
  (Spec.preimage (R.fiberMap a x ≫ (R.geometricFiber a).hom ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))))).hom

def lieCharacter (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)) :
    NumberField.RingOfIntegers E →+* R.fiberField a x :=
  (R.fiberScalar a x).comp
    (PadicInt.toZMod.comp (j.localCharacter M.extendedEmbedding τ))

/-- Actual dual-number Lie eigenspaces, as in the PEL moduli problem. -/
def HasLieRank (a : M.Family) (x : R.geom a) (τ : Gal(E/ℚ)) (r : ℕ) : Prop :=
  AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (R.fiberAbelian a x) (R.fiberAction a x) (R.lieCharacter a x τ) r

/-- The same geometric p-torsion count used in the Openness specification. -/
def IsOrdinary (a : M.Family) (x : R.geom a) : Prop :=
  IsOrdinaryAt q (R.abelian a).scheme x

def ordinaryLocus (a : M.Family) : Set (R.geom a) := {x | R.IsOrdinary a x}

omit [IsGalois ℚ E] in
theorem geometricFiber_smooth (a : M.Family)
    [Smooth (M.integral a).toOver.hom] : Smooth (R.geometricFiber a).hom :=
  inferInstanceAs (Smooth (pullback.snd (M.integral a).toOver.hom R.geometricBase))

omit [IsGalois ℚ E] in
theorem geometricFiber_proper (a : M.Family)
    [IsProper (M.integral a).toOver.hom] : IsProper (R.geometricFiber a).hom :=
  inferInstanceAs (IsProper (pullback.snd (M.integral a).toOver.hom R.geometricBase))

end GoodIntegralReduction
end RankThreePELModel

end

/-! Signature calculations for the actual PEL datum in CMPoints. -/

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ}

def pairedEmbedding (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (p : Fin s × Bool) : E →+* ℂ :=
  if p.2 then (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings p.1)).toRingHom
  else (P.embeddings p.1).toRingHom

theorem pairedEmbedding_injective (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) : Function.Injective (pairedEmbedding P) := by
  intro a b h
  apply hP.1.1
  ext x
  have hh := congrArg (fun f : E →+* ℂ => f x) h
  cases ha : a.2 <;> cases hb : b.2 <;>
    simpa [pairedEmbedding, ha, hb] using hh

theorem rationalConjugation_mul_self :
    Arithmetic.rationalConjugation E * Arithmetic.rationalConjugation E = 1 := by
  ext x
  exact NumberField.IsCMField.complexConj_apply_apply E x

theorem rationalConjugation_ne_one : Arithmetic.rationalConjugation E ≠ 1 := by
  intro h
  apply NumberField.IsCMField.complexConj_ne_one E
  ext x
  exact congrArg (fun g : Gal(E/ℚ) => g x) h

/-- Choose one element of every conjugate pair, with conjugation itself chosen. -/
theorem exists_conjugate_representatives :
    ∃ chosen : Set Gal(E/ℚ), Arithmetic.rationalConjugation E ∈ chosen ∧
      ∀ τ, τ ∈ chosen ↔ Arithmetic.rationalConjugation E * τ ∉ chosen := by
  classical
  let : Fintype Gal(E/ℚ) := Fintype.ofFinite _
  let e := Fintype.equivFin Gal(E/ℚ)
  let c := Arithmetic.rationalConjugation E
  have hcc : c * c = 1 := rationalConjugation_mul_self
  have hne (τ : Gal(E/ℚ)) : e τ ≠ e (c * τ) := by
    intro h
    have hh : 1 * τ = c * τ := by simpa using e.injective h
    exact rationalConjugation_ne_one (mul_right_cancel hh).symm
  have hinv (τ : Gal(E/ℚ)) : c * (c * τ) = τ := by rw [← mul_assoc, hcc, one_mul]
  by_cases hc : e c < e 1
  · refine ⟨{τ | e τ < e (c * τ)}, ?_, ?_⟩
    · change e c < e (c * c)
      rwa [hcc]
    · intro τ
      change e τ < e (c * τ) ↔ ¬e (c * τ) < e (c * (c * τ))
      rw [hinv]
      exact ⟨not_lt_of_gt, fun h => lt_of_le_of_ne (le_of_not_gt h) (hne τ)⟩
  · refine ⟨{τ | e (c * τ) < e τ}, ?_, ?_⟩
    · change e (c * c) < e c
      rw [hcc]
      exact lt_of_le_of_ne (le_of_not_gt hc) (by
        intro h
        exact rationalConjugation_ne_one (e.injective h).symm)
    · intro τ
      change e (c * τ) < e τ ↔ ¬e (c * (c * τ)) < e (c * τ)
      rw [hinv]
      exact ⟨not_lt_of_gt, fun h => lt_of_le_of_ne (le_of_not_gt h) (hne τ).symm⟩

theorem embedding_conjugation (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) :
    P.μ.comp (Arithmetic.rationalConjugation E).toRingHom =
      pairedEmbedding P (P.distinguished, true) := by
  ext x
  exact NumberField.IsCMField.complexEmbedding_complexConj E P.μ x

theorem lieRank_of_label (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) (τ : Gal(E/ℚ)) (i : Fin s) (b : Bool)
    (hτ : P.μ.comp τ.toRingHom = pairedEmbedding P (i, b)) :
    P.lieRank τ = if b then 3 - P.firstLieRank i else P.firstLieRank i := by
  classical
  have hinj := pairedEmbedding_injective P hP
  have heq (j : Fin s) (d : Bool) :
      P.μ.comp τ.toRingHom = pairedEmbedding P (j, d) ↔ (i, b) = (j, d) := by
    rw [hτ]
    exact hinj.eq_iff
  unfold AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.lieRank
  have hf (j : Fin s) :
      P.μ.comp τ.toRingHom = (P.embeddings j).toRingHom ↔ (i, b) = (j, false) :=
    heq j false
  have ht (j : Fin s) :
      P.μ.comp τ.toRingHom = (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings j)).toRingHom ↔
        (i, b) = (j, true) := heq j true
  simp_rw [hf, ht]
  cases b <;> simp

theorem lieRank_identity (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) :
    P.lieRank 1 = 2 := by
  have h := lieRank_of_label P hP 1 P.distinguished false (by
    ext x
    rfl)
  simpa [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.firstLieRank] using h

theorem lieRank_conjugation (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) :
    P.lieRank (Arithmetic.rationalConjugation E) = 1 := by
  have h := lieRank_of_label P hP (Arithmetic.rationalConjugation E) P.distinguished true
    (embedding_conjugation P)
  simpa [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.firstLieRank] using h

theorem embedding_label_exists (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) (τ : Gal(E/ℚ)) :
    ∃ p : Fin s × Bool, P.μ.comp τ.toRingHom = pairedEmbedding P p := by
  obtain ⟨p, hp⟩ := hP.1.2 ((P.embeddings P.distinguished).comp τ.toAlgHom)
  refine ⟨p, ?_⟩
  ext x
  have he := congrArg (fun f : E →ₐ[ℚ] ℂ => f x) hp
  cases hb : p.2 <;>
    simpa [pairedEmbedding, hb, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ] using he.symm

theorem lieRank_away_from_changing_pair (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hP : P.IsAdmissible) (τ : Gal(E/ℚ))
    (h1 : τ ≠ 1) (hc : τ ≠ Arithmetic.rationalConjugation E) :
    P.lieRank τ = 0 ∨ P.lieRank τ = 3 := by
  obtain ⟨⟨i, b⟩, hτ⟩ := embedding_label_exists P hP τ
  have hi : i ≠ P.distinguished := by
    intro hi
    subst i
    cases b with
    | false =>
        apply h1
        ext x
        apply P.μ.injective
        exact congrArg (fun f : E →+* ℂ => f x) hτ
    | true =>
        apply hc
        ext x
        apply P.μ.injective
        exact congrArg (fun f : E →+* ℂ => f x) (hτ.trans (embedding_conjugation P).symm)
  rw [lieRank_of_label P hP τ i b hτ]
  cases b <;> cases hs : P.compactSigns i <;>
    simp [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.firstLieRank, hi, hs]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
