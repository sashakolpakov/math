import OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothScalarExtension
import OAI.AlgebraicGeometry.Comparison.Betti.Open.Image
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.LocalPartition

/-! # Restricted Smooth Sheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RestrictedSmoothSheaf.Godement

noncomputable section

section

/-! Smooth scalar functions on an open submanifold act on the literal restriction of the ambient smooth form sheaf. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def smoothRestrictionInclusion (O : Opens M) : TopCat.of O ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def smoothRestrictionOpen (O : Opens M) (V : Opens O) : Opens M :=
  (show Topology.IsOpenEmbedding (smoothRestrictionInclusion O) from O.isOpenEmbedding').functor.obj V

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem smoothRestrictionOpen_le (O : Opens M) (V : Opens O) : smoothRestrictionOpen O V ≤ O := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

def restrictedSmoothFormSheaf (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (O : Opens M) (n : ℕ) : ConstantSheafSections.ComplexSheaves (TopCat.of O) :=
  (Open.Image.openRestriction (smoothRestrictionInclusion O) O.isOpenEmbedding').obj (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n)

def restrictedSmoothFormSheafMultiply (O : Opens M) (n : ℕ) (f : O → ℂ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) :
    restrictedSmoothFormSheaf E M O n ⟶ restrictedSmoothFormSheaf E M O n :=
  ObjectProperty.homMk {
    app V := ModuleCat.ofHom (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction (Open.SmoothScalarExtension.Godement.openSmoothScalarExtension O f)
      ((Open.SmoothScalarExtension.Godement.openSmoothScalarExtension_smoothOn O f hf).mono (smoothRestrictionOpen_le O V.unop)))
    naturality := by
      intro V W i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_smulByFunction
        (leOfHom ((show Topology.IsOpenEmbedding (smoothRestrictionInclusion O) from O.isOpenEmbedding').functor.map i.unop))
        (Open.SmoothScalarExtension.Godement.openSmoothScalarExtension O f)
        ((Open.SmoothScalarExtension.Godement.openSmoothScalarExtension_smoothOn O f hf).mono (smoothRestrictionOpen_le O V.unop)) a).symm }

theorem restrictedSmoothFormSheafMultiply_apply (O : Opens M) (n : ℕ) (f : O → ℂ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) (V : Opens O)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (smoothRestrictionOpen O V) n)
    (x : smoothRestrictionOpen O V) :
    (show Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (smoothRestrictionOpen O V) n from
      (restrictedSmoothFormSheafMultiply O n f hf).hom.app (op V) a) x =
      Open.SmoothScalarExtension.Godement.openSmoothScalarExtension O f x.val • a x := by
  exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction_apply (Open.SmoothScalarExtension.Godement.openSmoothScalarExtension O f)
    ((Open.SmoothScalarExtension.Godement.openSmoothScalarExtension_smoothOn O f hf).mono (smoothRestrictionOpen_le O V)) a x

end

section

/-! Supported smooth scalar actions on the actual restricted form sheaf have the required local finite-sum identities. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff BigOperators

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem restrictedSmoothFormSheafMultiply_vanishesOn (O : Opens M) (n : ℕ) (f : O → ℂ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) (W : Opens O) (hzero : ∀ x ∈ W, f x = 0) :
    Godement.Locality.VanishesOn (restrictedSmoothFormSheafMultiply O n f hf) W := by
  intro V hVW
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (smoothRestrictionOpen O V) n at a
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext (U := smoothRestrictionOpen O V)
  intro x
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction (Open.SmoothScalarExtension.Godement.openSmoothScalarExtension O f)
    ((Open.SmoothScalarExtension.Godement.openSmoothScalarExtension_smoothOn O f hf).mono (smoothRestrictionOpen_le O V)) a x = 0
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction_apply]
  obtain ⟨y, hy, hxy⟩ := x.property
  have hz : Open.SmoothScalarExtension.Godement.openSmoothScalarExtension O f x.val = 0 :=
    (congrArg (Open.SmoothScalarExtension.Godement.openSmoothScalarExtension O f) hxy.symm).trans
      ((Open.SmoothScalarExtension.Godement.openSmoothScalarExtension_apply O f y).trans (hzero y (hVW hy)))
  rw [hz]
  exact zero_smul ℂ (a x)

theorem restrictedSmoothFormSheafMultiply_local_sum {κ : Type*} (O : Opens M) (n : ℕ)
    (f : κ → O → ℂ) (hf : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (f i))
    (s : Finset κ) (W : Opens O) (hsum : ∀ x ∈ W, ∑ i ∈ s, f i x = 1) :
    Godement.Locality.VanishesOn ((∑ i ∈ s, restrictedSmoothFormSheafMultiply O n (f i) (hf i)) - 𝟙 _) W := by
  intro V hVW
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (smoothRestrictionOpen O V) n at a
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext (U := smoothRestrictionOpen O V)
  intro x
  let ev : (restrictedSmoothFormSheaf E M O n ⟶ restrictedSmoothFormSheaf E M O n) →+
      (TangentSpace 𝓘(ℝ, E) x.val [⋀^Fin n]→L[ℝ] ℂ) :=
    { toFun := fun g => (show Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (smoothRestrictionOpen O V) n from
        g.hom.app (op V) a) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev ((∑ i ∈ s, restrictedSmoothFormSheafMultiply O n (f i) (hf i)) - 𝟙 _) = 0
  rw [map_sub, map_sum]
  change (∑ i ∈ s, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction (Open.SmoothScalarExtension.Godement.openSmoothScalarExtension O (f i))
    ((Open.SmoothScalarExtension.Godement.openSmoothScalarExtension_smoothOn O (f i) (hf i)).mono (smoothRestrictionOpen_le O V)) a x) - a x = 0
  simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction_apply]
  obtain ⟨y, hy, hxy⟩ := x.property
  have hs : (∑ i ∈ s, Open.SmoothScalarExtension.Godement.openSmoothScalarExtension O (f i) x.val) = 1 :=
    (Finset.sum_congr rfl (fun i _ =>
      (congrArg (Open.SmoothScalarExtension.Godement.openSmoothScalarExtension O (f i)) hxy.symm).trans
        (Open.SmoothScalarExtension.Godement.openSmoothScalarExtension_apply O (f i) y))).trans (hsum y (hVW hy))
  rw [← Finset.sum_smul, hs, one_smul, sub_self]

end

/-! Smooth partitions on an open submanifold act directly on the literal restriction of its ambient form sheaf. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite Set
open scoped _root_.Manifold ContDiff BigOperators _root_.Topology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem exists_restrictedSmoothFormSheaf_locally_finite_partition (O : Opens M) [SigmaCompactSpace O]
    {κ : Type*} (U : κ → Opens O) (hU : ∀ x, ∃ i, x ∈ U i) (n : ℕ) :
    ∃ (V : κ → Opens O)
      (f : κ → (restrictedSmoothFormSheaf E M O n ⟶ restrictedSmoothFormSheaf E M O n)),
      (∀ i, U i ⊔ V i = ⊤) ∧ (∀ i, Godement.Locality.VanishesOn (f i) (V i)) ∧
      ∀ x : O, ∃ W : Opens O, x ∈ W ∧ ∃ s : Finset κ,
        (∀ i, i ∉ s → W ≤ V i) ∧ Godement.Locality.VanishesOn ((∑ i ∈ s, f i) - 𝟙 _) W := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, E)) isClosed_univ (fun i => (U i : Set O)) (fun i => (U i).isOpen)
      (by intro x _; exact mem_iUnion.mpr (hU x))
  let g := Analysis.DifferentialForms.Manifold.FinitePartition.complexPartitionFunction ρ
  have hg := Analysis.DifferentialForms.Manifold.FinitePartition.complexPartitionFunction_smooth ρ
  let V : κ → Opens O := fun i => ⟨(tsupport (g i))ᶜ, (isClosed_tsupport (g i)).isOpen_compl⟩
  refine ⟨V, fun i => restrictedSmoothFormSheafMultiply O n (g i) (hg i), ?_, ?_, ?_⟩
  · intro i
    apply top_le_iff.mp
    intro x _
    by_cases hx : x ∈ tsupport (g i)
    · exact Or.inl (hρ i ((Analysis.DifferentialForms.Manifold.FinitePartition.complexPartitionFunction_tsupport ρ i) ▸ hx))
    · exact Or.inr hx
  · intro i
    apply restrictedSmoothFormSheafMultiply_vanishesOn
    intro x hx
    exact image_eq_zero_of_notMem_tsupport hx
  · intro x
    obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp (ρ.eventually_fintsupport_subset x)
    refine ⟨⟨W, hWo⟩, hxW, ρ.fintsupport x, ?_, ?_⟩
    · intro i hi y hy hys
      have hs : y ∈ tsupport (ρ i) := (Analysis.DifferentialForms.Manifold.FinitePartition.complexPartitionFunction_tsupport ρ i) ▸ hys
      exact hi (hW hy ((ρ.mem_fintsupport_iff y i).mpr hs))
    · apply restrictedSmoothFormSheafMultiply_local_sum
      intro y hy
      have hs : ∑ i ∈ ρ.fintsupport x, ρ i y = 1 :=
        ρ.sum_finsupport' y (mem_univ y) ((ρ.finsupport_subset_fintsupport y).trans (hW hy))
      change ∑ i ∈ ρ.fintsupport x, (ρ i y : ℂ) = 1
      exact_mod_cast hs

end

end OAI.AlgebraicGeometry.Comparison.Betti.RestrictedSmoothSheaf.Godement
