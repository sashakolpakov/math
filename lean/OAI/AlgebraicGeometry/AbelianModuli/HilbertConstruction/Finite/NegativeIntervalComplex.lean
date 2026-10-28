import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SupportedComplexRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CochainTruncation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.FieldSupport

/-! # Negative Interval Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.NegativeIntervalComplex

noncomputable section

/-! Reindex a complex supported on the integer interval minus g through zero as a nonnegative cochain complex on zero through g. The actual terms, exactness, and field support are preserved. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u

def finiteNegativeIntervalEmbedding (g : ℕ) :
    ComplexShape.Embedding (CochainTruncation.finiteCochainShape g) (.up ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun i => (i.val : ℤ) - g)
    (fun i j h => by
      change (i.val : ℤ) - g = (j.val : ℤ) - g at h
      apply Fin.ext
      omega)
    (fun i j => by change i.val + 1 = j.val ↔ (i.val : ℤ) - g + 1 = (j.val : ℤ) - g; omega)

instance finiteNegativeIntervalEmbedding_isRelIff (g : ℕ) :
    (finiteNegativeIntervalEmbedding g).IsRelIff where
  rel' := by
    intro i j h
    change (i.val : ℤ) - g + 1 = (j.val : ℤ) - g at h
    change i.val + 1 = j.val
    omega

theorem finiteNegativeIntervalEmbedding_outside_iff (g : ℕ) (q : ℤ) :
    (∀ i, (finiteNegativeIntervalEmbedding g).f i ≠ q) ↔ q < -(g : ℤ) ∨ 0 < q := by
  constructor
  · intro h
    by_contra hn
    have hq : 0 ≤ q + g := by omega
    have hi : (q + g).toNat < g + 1 := by omega
    apply h ⟨(q + g).toNat, hi⟩
    change ((q + g).toNat : ℤ) - g = q
    omega
  · intro h i hi
    change (i.val : ℤ) - g = q at hi
    have := i.isLt
    omega

variable {R : Type u} [CommRing R]

def negativeIntervalCochain (K : CochainComplex (ModuleCat.{u} R) ℤ) (g : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (K.restriction (finiteNegativeIntervalEmbedding g)).extend (CochainTruncation.finiteCochainEmbedding g)

def negativeIntervalCochainXIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (g q : ℕ) (hq : q ≤ g) :
    (negativeIntervalCochain K g).X q ≅ K.X ((q : ℤ) - g) :=
  (K.restriction (finiteNegativeIntervalEmbedding g)).extendXIso
    (CochainTruncation.finiteCochainEmbedding g) (i := ⟨q, by omega⟩) rfl

theorem negativeIntervalCochain_finite_free
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (g : ℕ)
    (hfin : ∀ i, Module.Finite R (K.X i)) (hfree : ∀ i, Module.Free R (K.X i)) :
    ∀ q, Module.Finite R ((negativeIntervalCochain K g).X q) ∧
      Module.Free R ((negativeIntervalCochain K g).X q) := by
  intro q
  by_cases hq : q ≤ g
  · have : Module.Finite R (K.X ((q : ℤ) - g)) := hfin _
    have : Module.Free R (K.X ((q : ℤ) - g)) := hfree _
    let e := (negativeIntervalCochainXIso K g q hq).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  · have : Subsingleton ((negativeIntervalCochain K g).X q) :=
      ModuleCat.subsingleton_of_isZero
        ((K.restriction (finiteNegativeIntervalEmbedding g)).isZero_extend_X (CochainTruncation.finiteCochainEmbedding g) q
          ((CochainTruncation.finiteCochainEmbedding_outside_iff g q).mpr (Nat.lt_of_not_ge hq)))
    exact ⟨inferInstance, inferInstance⟩

theorem negativeIntervalCochain_exactAt_iff
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (g q : ℕ) (hq : q ≤ g)
    (hbound : ∀ i, i < -(g : ℤ) ∨ 0 < i → IsZero (K.X i)) :
    (negativeIntervalCochain K g).ExactAt q ↔ K.ExactAt ((q : ℤ) - g) := by
  let e := finiteNegativeIntervalEmbedding g
  let j : Fin (g + 1) := ⟨q, by omega⟩
  let : K.IsStrictlySupported e := {
    isZero := fun i hi => hbound i ((finiteNegativeIntervalEmbedding_outside_iff g i).mp hi) }
  exact ((K.restriction e).extend_exactAt_iff (CochainTruncation.finiteCochainEmbedding g) (j := j) rfl).trans
    (SupportedComplexRestriction.strictlySupported_restriction_exactAt_iff e K j)

theorem negativeIntervalCochain_fieldSupport
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (g : ℕ)
    (hbound : ∀ i, i < -(g : ℤ) ∨ 0 < i → IsZero (K.X i)) (I : Ideal R)
    (hfield : ∀ (B : Type u) [Field B] [Algebra R B], ¬ I ≤ RingHom.ker (algebraMap R B) →
      (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) :
    Cochain.FieldSupport.CochainFieldSupport (negativeIntervalCochain K g) I := by
  intro B _ _ hnot
  let F := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B
  let KB := (F.mapHomologicalComplex (.up ℤ)).obj K
  let e := finiteNegativeIntervalEmbedding g
  let : KB.IsStrictlySupported e := {
    isZero := fun i hi => F.map_isZero (hbound i ((finiteNegativeIntervalEmbedding_outside_iff g i).mp hi)) }
  have hr : ((F.mapHomologicalComplex (CochainTruncation.finiteCochainShape g)).obj (K.restriction e)).Acyclic :=
    SupportedComplexRestriction.strictlySupported_restriction_acyclic e KB (hfield B hnot)
  have hB := Additive.ComplexExtension.additive_extend_acyclic F (K.restriction e) (CochainTruncation.finiteCochainEmbedding g) hr
  intro q
  exact (Base.ChangeTensorExactness.baseChange_exactAt_iff_tensor (negativeIntervalCochain K g) q).mp (hB q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.NegativeIntervalComplex
