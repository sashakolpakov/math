import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.Quotient

/-! # Integral Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.IntegralAction.Construction

noncomputable section

section

/-! The diagonal standard integral coordinate module is a full real
lattice in Minkowski space. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem full_integer_module_pi
    {E I : Type} [AddCommGroup E] [Module ℝ E] [Fintype I]
    (L : Submodule ℤ E) (hL : Submodule.span ℝ (L : Set E) = ⊤) :
    Submodule.span ℝ (Submodule.pi Set.univ (fun _ : I => L) : Set (I → E)) = ⊤ := by
  let M := Submodule.span ℝ (Submodule.pi Set.univ (fun _ : I => L) : Set (I → E))
  have hi (i : I) : ∀ x : E, Pi.single i x ∈ M := by
    have he : Submodule.span ℝ (L : Set E) ≤
        M.comap (LinearMap.single ℝ (fun _ : I => E) i) := by
      apply Submodule.span_le.mpr
      intro x hx
      apply Submodule.subset_span
      exact Submodule.le_comap_single_pi (fun _ : I => L) hx
    rw [hL] at he
    exact fun x => he (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ E))
  apply top_unique
  intro x _
  rw [← Finset.univ_sum_single x]
  exact Submodule.sum_mem M (fun i _ => hi i (x i))

theorem standard_vectorLatticeImage_eq_pi
    (k : Type) [Field k] [NumberField k] (n : ℕ) :
    IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module =
      Submodule.pi Set.univ (fun _ : Fin n => mixedEmbedding.integerLattice k) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩ i _
    have ha' : a ∈ Integral.Matrices.Construction.integralCoordinateLattice (R := 𝓞 k) n :=
      (Integral.Matrices.Construction.integralCoordinateLattice_eq_span (R := 𝓞 k) (k := k) n).symm ▸ ha
    obtain ⟨b, hb⟩ := (Integral.Matrices.Construction.mem_integralCoordinateLattice a).mp ha' i
    refine ⟨b, ?_⟩
    change mixedEmbedding k (b : k) = mixedEmbedding k (a i)
    exact congrArg (mixedEmbedding k) hb
  · intro hx
    have hi (i : Fin n) : ∃ a : 𝓞 k, mixedEmbedding k (a : k) = x i := hx i trivial
    choose a ha using hi
    refine ⟨fun i => (a i : k), ?_, ?_⟩
    · change (fun i => (a i : k)) ∈ Submodule.span (𝓞 k) (Set.range (Pi.basisFun k (Fin n)))
      rw [← Integral.Matrices.Construction.integralCoordinateLattice_eq_span]
      exact (Integral.Matrices.Construction.mem_integralCoordinateLattice _).mpr (fun i => ⟨a i, rfl⟩)
    · exact funext ha

theorem standard_vectorLatticeImage_full
    (k : Type) [Field k] [NumberField k] (n : ℕ) :
    Submodule.span ℝ (IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module :
      Set (Fin n → mixedSpace k)) = ⊤ := by
  rw [standard_vectorLatticeImage_eq_pi]
  exact full_integer_module_pi _ (IsZLattice.span_top (K := ℝ) (L := mixedEmbedding.integerLattice k))

theorem standard_vectorLatticeImage_isZLattice
    (k : Type) [Field k] [NumberField k] (n : ℕ) :
    let : DiscreteTopology (IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) :=
      IntegralLattice.Construction.vectorLatticeImage_discrete _ (IntegralLattice.FullLattice.standard k n).finite
    IsZLattice ℝ (IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) := by
  let : DiscreteTopology (IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) :=
    IntegralLattice.Construction.vectorLatticeImage_discrete _ (IntegralLattice.FullLattice.standard k n).finite
  exact ⟨standard_vectorLatticeImage_full k n⟩

end

/-! The real Minkowski action agrees with the rational matrix action,
and integral archimedean matrices preserve the standard real lattice. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem archimedeanMixedSL_diagonal
    {k : Type} [Field k] {n : ℕ} (g : Algebraic.SL n k) :
    Archimedean.Quotient.Construction.archimedeanMixedSL k n (Archimedean.ExteriorAction.Construction.fullArchimedeanSLMap k n g) =
      Matrix.SpecialLinearGroup.map (mixedEmbedding k) g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := k) (x := g i j)).symm

theorem archimedeanRealRepresentation_diagonal
    {k : Type} [Field k] {n : ℕ} (g : Algebraic.SL n k) (x : Fin n → k) :
    Archimedean.Quotient.Construction.archimedeanRealRepresentation k n (Archimedean.ExteriorAction.Construction.fullArchimedeanSLMap k n g)
        (IntegralLattice.Construction.vectorMixedEmbedding (k := k) n x) =
      IntegralLattice.Construction.vectorMixedEmbedding (k := k) n (Matrix.SpecialLinearGroup.toLin' g x) := by
  change Matrix.SpecialLinearGroup.toLin'
    (Archimedean.Quotient.Construction.archimedeanMixedSL k n (Archimedean.ExteriorAction.Construction.fullArchimedeanSLMap k n g)) (IntegralLattice.Construction.vectorMixedEmbedding (k := k) n x) = _
  rw [archimedeanMixedSL_diagonal]
  funext i
  change (∑ j, mixedEmbedding k (g i j) * mixedEmbedding k (x j)) =
    mixedEmbedding k (∑ j, g i j * x j)
  simp only [map_sum, map_mul]

theorem integral_archimedean_preserves_minkowski
    {k : Type} [Field k] [NumberField k] {n : ℕ} {g : Archimedean.ExteriorAction.Construction.FullArchimedeanSL k n}
    (hg : g ∈ Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n) {x : Fin n → mixedSpace k}
    (hx : x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module) :
    Archimedean.Quotient.Construction.archimedeanRealRepresentation k n g x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module := by
  obtain ⟨A, rfl⟩ := hg
  obtain ⟨a, ha, rfl⟩ := hx
  let q := Matrix.SpecialLinearGroup.map (algebraMap (𝓞 k) k) A
  refine ⟨Matrix.SpecialLinearGroup.toLin' q a, ?_, (archimedeanRealRepresentation_diagonal q a).symm⟩
  have he : (IntegralLattice.FullLattice.standard k n).module = Integral.Matrices.Construction.integralCoordinateLattice (R := 𝓞 k) n :=
    (Integral.Matrices.Construction.integralCoordinateLattice_eq_span (R := 𝓞 k) (k := k) n).symm
  rw [he] at ha ⊢
  exact Integral.Matrices.Construction.specialLinear_integralCoordinateLattice_mem A ha

theorem integral_archimedean_preserves_minkowski_iff
    {k : Type} [Field k] [NumberField k] {n : ℕ} {g : Archimedean.ExteriorAction.Construction.FullArchimedeanSL k n}
    (hg : g ∈ Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n) (x : Fin n → mixedSpace k) :
    Archimedean.Quotient.Construction.archimedeanRealRepresentation k n g x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module ↔
      x ∈ IntegralLattice.Construction.vectorLatticeImage (IntegralLattice.FullLattice.standard k n).module := by
  constructor
  · intro hx
    have hi := integral_archimedean_preserves_minkowski ((Archimedean.ExteriorAction.Construction.fullArchimedeanIntegralSL k n).inv_mem hg) hx
    have he : Archimedean.Quotient.Construction.archimedeanRealRepresentation k n g⁻¹ (Archimedean.Quotient.Construction.archimedeanRealRepresentation k n g x) = x := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    exact he ▸ hi
  · exact integral_archimedean_preserves_minkowski hg

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.IntegralAction.Construction
