import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks

/-! # PEL Adapters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Exact adapters to ReferenceFamily's ring-action, Rosati, and Lie-signature data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}

/-- A ReferenceFamily action gives a ring homomorphism to actual integral endomorphisms. -/
def PELAdapters.actionToEnd {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (a : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) :
    R →+* End.IntegralEnd A.scheme where
  toFun r := End.endOfSchemeMap A.scheme (a.map r)
  map_zero' := by
    apply End.endSchemeMap_injective A.scheme
    rw [End.endSchemeMap_ofSchemeMap, a.map_zero, BaseChange.endSchemeMap_zero]
  map_one' := by
    apply End.endSchemeMap_injective A.scheme
    rw [End.endSchemeMap_ofSchemeMap, a.map_one, BaseChange.endSchemeMap_one]
  map_add' r s := by
    apply End.endSchemeMap_injective A.scheme
    rw [End.endSchemeMap_ofSchemeMap, a.map_add, BaseChange.endSchemeMap_add,
      End.endSchemeMap_ofSchemeMap, End.endSchemeMap_ofSchemeMap]
  map_mul' r s := by
    apply End.endSchemeMap_injective A.scheme
    rw [End.endSchemeMap_ofSchemeMap, a.map_mul, BaseChange.endSchemeMap_mul,
      End.endSchemeMap_ofSchemeMap, End.endSchemeMap_ofSchemeMap]

/-- Recover the ReferenceFamily action by evaluating natural transformations on the
identity point. This is the proved scheme-endomorphism equivalence. -/
def PELAdapters.actionFromEnd {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (a : R →+* End.IntegralEnd A.scheme) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A where
  map r := End.endSchemeMap A.scheme (a r)
  preservesGroup r := inferInstance
  map_zero := by rw [map_zero, BaseChange.endSchemeMap_zero]
  map_one := by rw [map_one, BaseChange.endSchemeMap_one]
  map_add r s := by rw [map_add, BaseChange.endSchemeMap_add]
  map_mul r s := by rw [map_mul, BaseChange.endSchemeMap_mul]

@[simp]
theorem PELAdapters.actionToEnd_schemeMap {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (a : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (r : R) :
    End.endSchemeMap A.scheme (PELAdapters.actionToEnd a r) = a.map r :=
  End.endSchemeMap_ofSchemeMap _ _

@[simp]
theorem PELAdapters.actionToEnd_fromEnd {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (a : R →+* End.IntegralEnd A.scheme) : PELAdapters.actionToEnd (PELAdapters.actionFromEnd a) = a := by
  apply RingHom.ext
  intro r
  apply End.endSchemeMap_injective A.scheme
  exact PELAdapters.actionToEnd_schemeMap (PELAdapters.actionFromEnd a) r

variable {E : Type u} [Field E] [NumberField E] [NumberField.IsCMField E]

/-- The TateComparison Rosati condition is exactly the one used by ReferenceFamily. -/
theorem PELAdapters.rosati_iff {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (a : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian) :
    (PEL.PELFamilyData.ofPolarized A (PELAdapters.actionToEnd a)).IsRosatiCompatible
        (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom ↔
      AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A a := by
  unfold PEL.PELFamilyData.IsRosatiCompatible PEL.PELFamilyData.IsPoincareDual
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation
  dsimp only [PEL.PELFamilyData.ofPolarized]
  simp only [PELAdapters.actionToEnd_schemeMap]
  constructor
  · intro h b
    obtain ⟨bd, hdual, hpol⟩ := h b
    refine ⟨End.endSchemeMap A.dual.abelian.scheme bd, inferInstance, ?_, ?_⟩
    · exact hdual.symm
    · exact hpol
  · intro h b
    obtain ⟨bd, hbd, hdual, hpol⟩ := h b
    let : IsMonHom bd := hbd
    refine ⟨End.endOfSchemeMap A.dual.abelian.scheme bd, ?_, ?_⟩
    · simpa only [End.endSchemeMap_ofSchemeMap] using hdual.symm
    · rw [End.endSchemeMap_ofSchemeMap]
      exact hpol

variable {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

/-- The prescribed Lie signature is tested on the actual dual-number
points at the identity of every geometric fiber. -/
def PEL.PELFamilyData.HasPrescribedLieSignature
    (baseAction : NumberField.RingOfIntegers E →+* Γ(S, ⊤))
    (D : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N S) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S)
    (τ : E ≃ₐ[ℚ] E),
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (D.abelian.pullback t)
      (PELAdapters.actionFromEnd ((BaseChange.endBaseChange D.abelian.scheme t).comp D.action))
      (((Scheme.ΓSpecIso (.of k)).hom.hom.comp (t.appTop.hom.comp baseAction)).comp
        (NumberField.RingOfIntegers.mapAlgEquiv τ).toRingHom)
      (P.lieRank τ)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
