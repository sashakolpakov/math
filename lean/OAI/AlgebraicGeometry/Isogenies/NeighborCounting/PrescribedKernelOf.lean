import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels

/-! # Prescribed Kernel Of -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Components

/-! Recover literal coefficient components directly from the independent
canonical FrobeniusKernel kernel prescription, on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ProjectorLevels

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

omit [IsAlgClosed k] in
theorem prescribedBlockComponent_val (n : ℕ) (τ : Gal(E/ℚ)) (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x).val =
      x.val ≫ ρ.map (j.projector iota hsplit n τ) := rfl

omit [IsAlgClosed k] in
theorem prescribedChosenPoint_val (n : ℕ) (τ : Gal(E/ℚ))
    (H : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
    (T : Over (Spec (.of k))) (h : T ⟶ H.group.X) :
    (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T h).val =
      h ≫ H.inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n τ := by
  change (h ≫ H.inclusion.hom.hom) ≫ _ = _
  exact Category.assoc _ _ _

variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

theorem prescribed_full_kernel_killed (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme)
    (ha : AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T a) :
    a ^ (q ^ n) = 1 := by
  obtain ⟨x, rfl, _⟩ := ha
  exact x.property

theorem prescribed_full_kernel_lower_support {m : ℕ} (hnm : n ≤ m) (τ : Gal(E/ℚ))
    (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme)
    (hs : a ≫ ρ.map (j.projector iota hsplit m τ) = a)
    (ha : AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T a) :
    a ≫ ρ.map (j.projector iota hsplit n τ) = a := by
  have hk := prescribed_full_kernel_killed j iota hsplit A ρ n s labels H T a ha
  have hc := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A.abelian ρ _ _ (q ^ n)
    (by simpa only [Nat.cast_pow] using ProjectorLevels.projector_level_congruence j iota hsplit hnm τ) T a hk
  exact hc.symm.trans hs

theorem prescribed_chosen_component_higher {m : ℕ} (hnm : n ≤ m) (v : Fin s)
    (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme)
    (hs : a ≫ ρ.map (j.projector iota hsplit m (labels (v, false))) = a)
    (ha : AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T a) :
    ∃ h : T ⟶ (H v).group.X,
      h ≫ (H v).inclusion.hom.hom ≫
        AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false)) = a := by
  have hl := prescribed_full_kernel_lower_support j iota hsplit A ρ n s labels H hnm
    (labels (v, false)) T a hs ha
  obtain ⟨x, hx, hp⟩ := ha
  obtain ⟨h, hh⟩ := (hp v).1
  refine ⟨h, ?_⟩
  have hc := congrArg Subtype.val hh
  rw [prescribedChosenPoint_val, prescribedBlockComponent_val, hx, hl] at hc
  exact hc

end AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Components

namespace AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Containment

/-! Every prescribed chosen subgroup lies in the complete canonical
kernel. Opposite pairing conditions hold after every base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Components

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}

omit [IsAlgClosed k] in
theorem originalTorsionSheafPoint_one (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (m : ℕ) (T : Over (Spec (.of k))) : AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint A m T 1 = 1 := by
  unfold AbelianScheme.FrobeniusKernel.Prescription.Construction.originalTorsionSheafPoint
  rw [map_one]
  exact map_one _

theorem canonicalTorsionOrthogonal_one_right
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (m : ℕ) (hm : 0 < m) (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor m).obj (.op T)) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal A m hm T x 1 := by
  unfold AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal
  rw [originalTorsionSheafPoint_one, AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.adjoint_value]
  exact map_one _

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

omit [IsAlgClosed k] in
theorem prescribedChosenPoint_one (n : ℕ) (τ : Gal(E/ℚ))
    (H : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
    (T : Over (Spec (.of k))) : AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T 1 = 1 := by
  apply Subtype.ext
  rw [Components.prescribedChosenPoint_val, MonObj.one_comp]
  rfl

omit [IsAlgClosed k] in
theorem prescribedChosenPoint_component_self (n : ℕ) (τ : Gal(E/ℚ))
    (H : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
    (T : Over (Spec (.of k))) (h : T ⟶ H.group.X) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T
      (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T h) =
        AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T h := by
  apply Subtype.ext
  exact PELModuli.CMPoints.BlockDecomposition.block_projector_self j iota hsplit A.abelian ρ n τ T
    ((AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T)
      (h ≫ H.inclusion.hom.hom))

omit [IsAlgClosed k] in
theorem prescribedChosenPoint_component_other (n : ℕ) (τ υ : Gal(E/ℚ)) (hτυ : τ ≠ υ)
    (H : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
    (T : Over (Spec (.of k))) (h : T ⟶ H.group.X) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n υ T
      (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T h) = 1 := by
  apply Subtype.ext
  exact PELModuli.CMPoints.BlockDecomposition.block_projector_other j iota hsplit A.abelian ρ n τ υ hτυ T
    ((AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).hom.app (.op T)
      (h ≫ H.inclusion.hom.hom))

omit [IsAlgClosed k] in
theorem prescribedChosenPoint_natural (n : ℕ) (τ : Gal(E/ℚ))
    (H : AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
    {T U : Over (Spec (.of k))} (t : U ⟶ T) (h : T ⟶ H.group.X) :
    (A.abelian.torsionFunctor (q ^ n)).map t.op
      (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T h) =
        AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H U (t ≫ h) := by
  apply Subtype.ext
  change t ≫ (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n τ H T h).val = _
  rw [Components.prescribedChosenPoint_val, Components.prescribedChosenPoint_val, Category.assoc]

theorem prescribed_full_kernel_contains_chosen (n s : ℕ)
    (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
    (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
    (v : Fin s) (T : Over (Spec (.of k))) (h : T ⟶ (H v).group.X) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T
      (h ≫ (H v).inclusion.hom.hom ≫
        AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A.abelian ρ n (labels (v, false))) := by
  refine ⟨AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) T h,
    Components.prescribedChosenPoint_val j iota hsplit A ρ n (labels (v, false)) (H v) T h, ?_⟩
  intro w
  constructor
  · by_cases hvw : v = w
    · subst w
      exact ⟨h, (prescribedChosenPoint_component_self j iota hsplit A ρ n
        (labels (v, false)) (H v) T h).symm⟩
    · refine ⟨1, ?_⟩
      rw [prescribedChosenPoint_one, prescribedChosenPoint_component_other]
      exact fun he => hvw (congrArg Prod.fst (labels.injective he))
  · intro U t h'
    rw [prescribedChosenPoint_natural, prescribedChosenPoint_component_other]
    · exact canonicalTorsionOrthogonal_one_right A _ _ U _
    · intro he
      have hb := congrArg Prod.snd (labels.injective he)
      cases hb

end AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Containment

namespace AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Opposite

/-! The opposite restriction of the full canonical prescription is
exactly its all-test annihilator condition, with the original q-power
bound. No Cartier-duality comparison is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Components OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Containment

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

omit [IsAlgClosed k] in
theorem prescribed_component_fixed (n : ℕ) (τ : Gal(E/ℚ)) (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T))
    (hs : x.val ≫ ρ.map (j.projector iota hsplit n τ) = x.val) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x = x :=
  Subtype.ext hs

omit [IsAlgClosed k] in
theorem prescribed_component_other_of_fixed (n : ℕ) (τ υ : Gal(E/ℚ)) (hτυ : τ ≠ υ)
    (T : Over (Spec (.of k))) (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T))
    (hs : x.val ≫ ρ.map (j.projector iota hsplit n τ) = x.val) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n υ T x = 1 := by
  apply Subtype.ext
  have h := PELModuli.CMPoints.BlockDecomposition.projector_orthogonal_on_torsion j iota hsplit A.abelian ρ n τ υ hτυ T x.val x.property
  rw [hs] at h
  exact h

omit [IsAlgClosed k] in
theorem prescribed_support_natural (n : ℕ) (τ : Gal(E/ℚ)) {T U : Over (Spec (.of k))}
    (t : U ⟶ T) (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T))
    (hs : x.val ≫ ρ.map (j.projector iota hsplit n τ) = x.val) :
    ((A.abelian.torsionFunctor (q ^ n)).map t.op x).val ≫
      ρ.map (j.projector iota hsplit n τ) = ((A.abelian.torsionFunctor (q ^ n)).map t.op x).val := by
  change (t ≫ x.val) ≫ _ = t ≫ x.val
  rw [Category.assoc, hs]

variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (H : ∀ v : Fin s, AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

theorem prescribed_full_kernel_on_opposite (v : Fin s) (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T))
    (hs : x.val ≫ ρ.map (j.projector iota hsplit n (labels (v, true))) = x.val) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T x.val ↔
      ∀ (U : Over (Spec (.of k))) (t : U ⟶ T) (h : U ⟶ (H v).group.X),
        AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
          (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U h)
          ((A.abelian.torsionFunctor (q ^ n)).map t.op x) := by
  constructor
  · rintro ⟨y, hy, hp⟩ U t h
    have hxy : y = x := Subtype.ext hy
    subst y
    have ho := (hp v).2 U t h
    rw [prescribed_component_fixed j iota hsplit A ρ n (labels (v, true)) U _
      (prescribed_support_natural j iota hsplit A ρ n (labels (v, true)) t x hs)] at ho
    exact ho
  · intro ho
    refine ⟨x, rfl, ?_⟩
    intro w
    constructor
    · refine ⟨1, ?_⟩
      rw [Containment.prescribedChosenPoint_one, prescribed_component_other_of_fixed j iota hsplit A ρ n
        (labels (v, true)) (labels (w, false)) _ T x hs]
      intro he
      have hb := congrArg Prod.snd (labels.injective he)
      cases hb
    · intro U t h
      have ht := prescribed_support_natural j iota hsplit A ρ n (labels (v, true)) t x hs
      by_cases hvw : v = w
      · subst w
        rw [prescribed_component_fixed j iota hsplit A ρ n (labels (v, true)) U _ ht]
        exact ho U t h
      · rw [prescribed_component_other_of_fixed j iota hsplit A ρ n
          (labels (v, true)) (labels (w, true)) _ U _ ht]
        · exact Containment.canonicalTorsionOrthogonal_one_right A _ _ U _
        · exact fun he => hvw (congrArg Prod.fst (labels.injective he))

theorem prescribed_opposite_higher {m : ℕ} (hnm : n ≤ m) (v : Fin s)
    (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme)
    (hs : a ≫ ρ.map (j.projector iota hsplit m (labels (v, true))) = a) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T a ↔
      ∃ x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T), x.val = a ∧
        ∀ (U : Over (Spec (.of k))) (t : U ⟶ T) (h : U ⟶ (H v).group.X),
          AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
            (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U h)
            ((A.abelian.torsionFunctor (q ^ n)).map t.op x) := by
  constructor
  · intro ha
    have hl := Components.prescribed_full_kernel_lower_support j iota hsplit A ρ n s labels H hnm
      (labels (v, true)) T a hs ha
    obtain ⟨x, hx, hp⟩ := ha
    refine ⟨x, hx, ?_⟩
    apply (prescribed_full_kernel_on_opposite j iota hsplit A ρ n s labels H v T x ?_).mp
    · exact ⟨x, rfl, hp⟩
    · simpa only [hx] using hl
  · rintro ⟨x, rfl, ho⟩
    have hc := PELModuli.CMPoints.BlocksProjectors.action_eq_of_congruence A.abelian ρ _ _ (q ^ n)
      (by simpa only [Nat.cast_pow] using
        ProjectorLevels.projector_level_congruence j iota hsplit hnm (labels (v, true)))
      T x.val x.property
    exact (prescribed_full_kernel_on_opposite j iota hsplit A ρ n s labels H v T x
      (hc.symm.trans hs)).mpr ho

end AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedKernelOf.Opposite

end

end OAI
