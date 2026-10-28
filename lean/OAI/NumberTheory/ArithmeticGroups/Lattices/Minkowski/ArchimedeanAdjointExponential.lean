import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieEq
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.ExponentialConjugation
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialIntegration

/-! # Archimedean Adjoint Exponential -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.ArchimedeanAdjointExponential.Construction

noncomputable section

section

/-! The faithful Minkowski matrix exponential of a Lie-algebra element
is an actual point of the full archimedean algebraic group. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Operator
open _root_.NumberField _root_.NumberField.mixedEmbedding NormedSpace

theorem lieMixed_exp_complex_point
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A : Lie.MixedLattice.Construction.lieMixedSpan G) (v : InfinitePlace k) :
    ∃ g : G.Points ((InfinitePlace.Completion.extensionEmbedding v).comp
        (algebraMap k v.Completion)),
      (g.val : Matrix (Fin n) (Fin n) ℂ) =
        (LieEq.Construction.mixedComplexEvaluation v).mapMatrix (exp A.val) := by
  let ι := (InfinitePlace.Completion.extensionEmbedding v).comp (algebraMap k v.Completion)
  let φ := LieEq.Construction.mixedComplexEvaluation v
  have hA : A.val.map φ ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G ι) :=
    LieEq.Construction.lieMixedModule_mem_field_image G hG ι φ (LieEq.Construction.mixedComplexEvaluation_embedding v) A.val A.property
  let p := ExponentialIntegration.Construction.infinitesimalExponential (BaseChange.Construction.matrixGroupBaseChange G ι) ⟨A.val.map φ, hA⟩ 1
  have hp : p.val ∈ G.subgroup ℂ ι := by
    simpa only [BaseChange.Construction.matrixGroupBaseChange, RingHom.id_comp] using p.property
  refine ⟨⟨p.val, hp⟩, ?_⟩
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) (mixedSpace k)) :=
    NormedAlgebra.restrictScalars ℚ ℝ (Matrix (Fin n) (Fin n) (mixedSpace k))
  let : CompleteSpace (Matrix (Fin n) (Fin n) (mixedSpace k)) :=
    FiniteDimensional.complete ℝ (Matrix (Fin n) (Fin n) (mixedSpace k))
  have hφ : Continuous (φ.mapMatrix : Matrix (Fin n) (Fin n) (mixedSpace k) →
      Matrix (Fin n) (Fin n) ℂ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (LieEq.Construction.continuous_mixedComplexEvaluation v).comp
      ((continuous_apply j).comp (continuous_apply i))
  have he := NormedSpace.map_exp φ.mapMatrix hφ A.val
  change exp (1 • A.val.map φ) = φ.mapMatrix (exp A.val)
  simpa only [one_smul, RingHom.mapMatrix_apply] using! he.symm

theorem lieMixed_exp_completion_point
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A : Lie.MixedLattice.Construction.lieMixedSpan G) (v : InfinitePlace k) :
    ∃ g : G.Points (algebraMap k v.Completion),
      (g.val : Matrix (Fin n) (Fin n) v.Completion) =
        (QuadraticInvariant.Construction.mixedCompletionEvaluation v).mapMatrix (exp A.val) := by
  obtain ⟨gC, hgC⟩ := lieMixed_exp_complex_point G hG A v
  let ρ := InfinitePlace.Completion.extensionEmbedding v
  let M := (QuadraticInvariant.Construction.mixedCompletionEvaluation v).mapMatrix (exp A.val)
  have hM : ρ.mapMatrix M = (gC.val : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hgC]
    rfl
  have hdet : M.det = 1 := by
    apply ρ.injective
    rw [map_one, RingHom.map_det, hM, Matrix.SpecialLinearGroup.det_coe]
  let g : Algebraic.SL n v.Completion := ⟨M, hdet⟩
  have he : Matrix.SpecialLinearGroup.map ρ g = gC.val := Subtype.ext hM
  have hg : g ∈ G.subgroup v.Completion (algebraMap k v.Completion) := by
    have h := (Archimedean.Quotient.Construction.matrixGroup_mem_iff_scalar_extension
      (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion)) ρ g).mp
    apply h
    change Matrix.SpecialLinearGroup.map ρ g ∈
      G.subgroup ℂ (ρ.comp (algebraMap k v.Completion))
    rw [he]
    exact gC.property
  exact ⟨⟨g, hg⟩, rfl⟩

theorem lieMixed_exp_exists_archimedean
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A : Lie.MixedLattice.Construction.lieMixedSpan G) :
    ∃ g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G, (Archimedean.LieMem.Construction.archimedeanLieUnit G g).val = exp A.val := by
  choose gv hgv using lieMixed_exp_completion_point G hG A
  let g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G := ⟨fun v => (gv v).val, fun v => (gv v).property⟩
  refine ⟨g, ?_⟩
  ext i j : 1
  apply LieEq.Construction.mixedCompletionEvaluation_jointly_injective
  intro v
  have he := QuadraticInvariant.Construction.mixedCompletionEvaluation_matrix v g.val
  have hei := congrArg (fun M => M i j) he
  change QuadraticInvariant.Construction.mixedCompletionEvaluation v ((Archimedean.LieMem.Construction.archimedeanLieUnit G g).val i j) = (gv v).val i j at hei
  rw [hei]
  exact congrArg (fun M => M i j) (hgv v)

end

/-! Every intrinsic adjoint exponential is in the image of the actual
archimedean adjoint representation. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Operator
open _root_.NumberField _root_.NumberField.mixedEmbedding NormedSpace

local instance lieMixedSpan_normed_uniform_for_adj_exp
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    UniformSpace (Lie.MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace

local instance lieMixedSpan_normed_topology_for_adj_exp
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    TopologicalSpace (Lie.MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace

local instance lieMixedOperator_topologicalRing_for_adj_exp
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    IsTopologicalRing (Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing _
    (inferInstance : NonUnitalSeminormedRing (Lie.MixedLattice.Construction.lieMixedSpan G →L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G))

theorem archimedean_adjoint_exponential_in_image
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A : Lie.MixedLattice.Construction.lieMixedSpan G) :
    ∃ g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G,
      (Archimedean.LieMem.Construction.archimedeanLieRepresentation G hG g).toLinearMap =
        (exp (LieTangent.Construction.lieMixedContinuousBracket G hG A)).toLinearMap := by
  obtain ⟨g, hg⟩ := lieMixed_exp_exists_archimedean G hG A
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) (mixedSpace k)) :=
    NormedAlgebra.restrictScalars ℚ ℝ (Matrix (Fin n) (Fin n) (mixedSpace k))
  let : CompleteSpace (Matrix (Fin n) (Fin n) (mixedSpace k)) :=
    FiniteDimensional.complete ℝ (Matrix (Fin n) (Fin n) (mixedSpace k))
  have hi : exp A.val * exp (-A.val) = (1 : Matrix (Fin n) (Fin n) (mixedSpace k)) := by
    simpa only [add_neg_cancel, exp_zero] using!
      (exp_add_of_commute (Commute.refl A.val).neg_right).symm
  have hinv : ((Archimedean.LieMem.Construction.archimedeanLieUnit G g)⁻¹).val = exp (-A.val) := by
    calc
      ((Archimedean.LieMem.Construction.archimedeanLieUnit G g)⁻¹).val = ((Archimedean.LieMem.Construction.archimedeanLieUnit G g)⁻¹).val * 1 := (mul_one _).symm
      _ = ((Archimedean.LieMem.Construction.archimedeanLieUnit G g)⁻¹).val * (exp A.val * exp (-A.val)) := by rw [hi]
      _ = exp (-A.val) := by
        rw [← hg, ← mul_assoc]
        have hu : ((Archimedean.LieMem.Construction.archimedeanLieUnit G g)⁻¹).val * (Archimedean.LieMem.Construction.archimedeanLieUnit G g).val = 1 :=
          congrArg Units.val (inv_mul_cancel (Archimedean.LieMem.Construction.archimedeanLieUnit G g))
        rw [hu, one_mul]
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  change (Archimedean.LieMem.Construction.archimedeanLieEquiv G hG g X).val = (exp (LieTangent.Construction.lieMixedContinuousBracket G hG A) X).val
  calc
    _ = (Archimedean.LieMem.Construction.archimedeanLieUnit G g).val * X.val * ((Archimedean.LieMem.Construction.archimedeanLieUnit G g)⁻¹).val :=
      Archimedean.LieMem.Construction.archimedeanLieEquiv_apply G hG g X
    _ = exp A.val * X.val * exp (-A.val) := by rw [hg, hinv]
    _ = _ := (ExponentialConjugation.Construction.lieMixed_adjoint_exp_conjugation G hG A X).symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.ArchimedeanAdjointExponential.Construction
