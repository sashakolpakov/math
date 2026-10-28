import OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition
import Mathlib.FieldTheory.Normal.Closure

/-! # Common CM Field -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# A common Galois CM coefficient field

The compositum inside `ℂ` of the normal closures of a finite family of
number fields contains the images of all of their complex embeddings.
When the family is nonempty and consists of CM fields, this compositum is
CM: its restricted complex conjugation acts as conjugation under every
embedding, as can be checked on the generating CM subfields.
-/

open IntermediateField

variable {ι : Type*} (E : ι → Type*) [∀ i, Field (E i)] [∀ i, Algebra ℚ (E i)]

/-- The compositum of all conjugates of all fields in a family. -/
def CommonCMField.CM.conjugateCompositum : IntermediateField ℚ ℂ :=
  ⨆ i, normalClosure ℚ (E i) ℂ

namespace CommonCMField.CM.conjugateCompositum

/-- Every complex embedding of a component lands in the compositum. -/
theorem fieldRange_le (i : ι) (σ : E i →ₐ[ℚ] ℂ) :
    σ.fieldRange ≤ conjugateCompositum E :=
  σ.fieldRange_le_normalClosure.trans (le_iSup (fun i => normalClosure ℚ (E i) ℂ) i)

/-- An embedding of a component, with its codomain restricted to the common field. -/
def embedding (i : ι) (σ : E i →ₐ[ℚ] ℂ) : E i →ₐ[ℚ] conjugateCompositum E :=
  σ.codRestrict _ (fun x => fieldRange_le E i σ ⟨x, rfl⟩)

@[simp]
theorem embedding_coe (i : ι) (σ : E i →ₐ[ℚ] ℂ) (x : E i) :
    (embedding E i σ x : ℂ) = σ x := rfl

/-- Maps from the common field are determined by the original embedding images. -/
theorem algHom_ext {L : Type*} [Field L] [Algebra ℚ L]
    {f g : conjugateCompositum E →ₐ[ℚ] L}
    (h : ∀ i σ x, f (embedding E i σ x) = g (embedding E i σ x)) : f = g := by
  let J : IntermediateField ℚ (conjugateCompositum E) :=
    { f.toRingHom.eqLocusField g.toRingHom with
      algebraMap_mem' := fun q => (f.commutes q).trans (g.commutes q).symm }
  have hle : conjugateCompositum E ≤ J.map (conjugateCompositum E).val := by
    apply iSup_le
    intro i
    apply normalClosure_le_iff.mpr
    intro σ x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨embedding E i σ a, h i σ a, rfl⟩
  ext x
  obtain ⟨y, hy, heq⟩ := hle x.property
  have hxy : y = x := Subtype.ext heq
  exact hxy ▸ hy

variable [∀ i, NumberField (E i)]

instance normal : Normal ℚ (conjugateCompositum E) := by
  exact IntermediateField.normal_iSup ℚ ℂ _ (h := fun i =>
    (Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (F := ℚ) (K := E i) (L := ℂ) (fun _ => IsAlgClosed.splits _)).normal)

instance finiteDimensional [Finite ι] : FiniteDimensional ℚ (conjugateCompositum E) :=
  IntermediateField.finiteDimensional_iSup_of_finite

instance numberField [Finite ι] : NumberField (conjugateCompositum E) :=
  NumberField.of_module_finite ℚ _

instance isGalois : IsGalois ℚ (conjugateCompositum E) := {}

/-- Complex conjugation restricted to the normal compositum. -/
def conjugation : Gal(conjugateCompositum E/ℚ) :=
  (Complex.conjAe.restrictScalars ℚ).restrictNormal (conjugateCompositum E)

@[simp]
theorem conjugation_coe (x : conjugateCompositum E) :
    (conjugation E x : ℂ) = star (x : ℂ) :=
  AlgEquiv.restrictNormal_commutes _ _ x

variable [∀ i, NumberField.IsCMField (E i)]

/-- Conjugation restricts on each generating image to its intrinsic CM conjugation. -/
theorem conjugation_embedding (i : ι) (σ : E i →ₐ[ℚ] ℂ) (x : E i) :
    conjugation E (embedding E i σ x) =
      embedding E i σ (NumberField.IsCMField.complexConj (E i) x) := by
  apply Subtype.ext
  rw [conjugation_coe]
  exact (NumberField.IsCMField.complexEmbedding_complexConj
    (E i) σ.toRingHom x).symm

/-- Every embedding sees the same conjugation on the compositum. -/
theorem embedding_conjugation (φ : conjugateCompositum E →+* ℂ)
    (x : conjugateCompositum E) :
    φ (conjugation E x) = star (φ x) := by
  let f : conjugateCompositum E →ₐ[ℚ] ℂ :=
    { φ.comp (conjugation E).toRingHom with
      commutes' := RingHom.map_rat_algebraMap _ }
  let g : conjugateCompositum E →ₐ[ℚ] ℂ :=
    { (starRingEnd ℂ).comp φ with
      commutes' := RingHom.map_rat_algebraMap _ }
  have heq : f = g := algHom_ext E (fun i σ a => by
    change φ (conjugation E (embedding E i σ a)) = star (φ (embedding E i σ a))
    rw [conjugation_embedding]
    exact NumberField.IsCMField.complexEmbedding_complexConj (E i)
      (φ.comp (embedding E i σ).toRingHom) a)
  exact congrArg (fun h : conjugateCompositum E →ₐ[ℚ] ℂ => h x) heq

theorem isConj_conjugation (φ : conjugateCompositum E →+* ℂ) :
    NumberField.ComplexEmbedding.IsConj φ (conjugation E) := by
  ext x
  exact (embedding_conjugation E φ x).symm

instance isTotallyComplex [Nonempty ι] :
    NumberField.IsTotallyComplex (conjugateCompositum E) := by
  let i : ι := Classical.arbitrary ι
  let σ : E i →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let : Algebra (E i) (conjugateCompositum E) := (embedding E i σ).toAlgebra
  exact NumberField.isTotallyComplex_of_algebra (E i) _

/-- A nonempty compositum of conjugates of CM fields is itself CM. -/
instance isCMField [Nonempty ι] : NumberField.IsCMField (conjugateCompositum E) :=
  NumberField.IsCMField.of_forall_isConj _ (isConj_conjugation E)

end CommonCMField.CM.conjugateCompositum

/-- A finite family of CM fields has a common finite Galois CM field inside
`ℂ` containing every conjugate image. The family is allowed to be empty. -/
theorem CommonCMField.CM.exists_common_galois_cm_field [Finite ι] [∀ i, NumberField (E i)]
    [∀ i, NumberField.IsCMField (E i)] :
    ∃ K : IntermediateField ℚ ℂ, NumberField K ∧ IsGalois ℚ K ∧
      NumberField.IsCMField K ∧ ∀ i (σ : E i →ₐ[ℚ] ℂ), σ.fieldRange ≤ K := by
  rcases isEmpty_or_nonempty ι with h | h
  · have := h
    let F := CyclotomicField 4 ℚ
    have : IsCyclotomicExtension {4} ℚ F := CyclotomicField.isCyclotomicExtension 4 ℚ
    have : NumberField.IsCMField F :=
      IsCyclotomicExtension.Rat.isCMField F ⟨4, Set.mem_singleton 4, by norm_num⟩
    let K := CommonCMField.CM.conjugateCompositum (fun _ : Unit => F)
    refine ⟨K, inferInstance, inferInstance, inferInstance, ?_⟩
    exact fun i => isEmptyElim i
  · have := h
    exact ⟨CommonCMField.CM.conjugateCompositum E, inferInstance, inferInstance, inferInstance,
      CommonCMField.CM.conjugateCompositum.fieldRange_le E⟩

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (D : Decomposition.CM.CMDecomposition H)

/-- The actual CM decomposition admits a common Galois CM coefficient field,
even when its summands have different fields or there are no summands. -/
theorem Decomposition.CM.CMDecomposition.exists_common_galois_cm_field :
    ∃ K : IntermediateField ℚ ℂ, NumberField K ∧ IsGalois ℚ K ∧
      NumberField.IsCMField K ∧
        ∀ i (σ : (D.component i).field →ₐ[ℚ] ℂ), σ.fieldRange ≤ K := by
  let componentNumberFields : ∀ i, NumberField (D.component i).field :=
    fun i => (D.component i).cm.numberField
  let componentCMFields : ∀ i, NumberField.IsCMField (D.component i).field :=
    fun i => (D.component i).cm.cmField
  exact CommonCMField.CM.exists_common_galois_cm_field (fun i => (D.component i).field)

end

end OAI.AlgebraicGeometry.ComplexMultiplication
