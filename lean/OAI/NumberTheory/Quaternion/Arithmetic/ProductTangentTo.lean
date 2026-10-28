import OAI.NumberTheory.Quaternion.Arithmetic.EmbeddedCommensurability
import OAI.NumberTheory.Quaternion.Arithmetic.LocalProductTangent

/-! # Product Tangent To -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ProductTangentTo

noncomputable section

section

/-! Conjugation acts on the simultaneous local tangent span. Rational
commensurators therefore preserve this span over a common prime field. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F κ : Type} [Field F] [NumberField F] [Field κ] {n : ℕ} {ι : Type*}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : ι → HeightOneSpectrum (𝓞 F))
variable [∀ i, Algebra κ ((v i).adicCompletion F)]

def productMatrixConjugation (g : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) :
    (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)) →L[κ]
      (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)) :=
  ContinuousLinearMap.pi (fun i =>
    ((TangentCone.matrixConjugation (K := (v i).adicCompletion F) G (LocalAdeles.localEmbedding (Sum.inr (v i))) (g i)).restrictScalars κ).comp
      (ContinuousLinearMap.proj i))

theorem productMatrixConjugation_one (g : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) :
    productMatrixConjugation (κ := κ) G v g 1 = 1 := by
  funext i
  exact TangentCone.matrixConjugation_one G (LocalAdeles.localEmbedding (Sum.inr (v i))) (g i)

theorem continuous_productMatrixConjugation_point
    (X : ∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)) :
    Continuous (fun g => productMatrixConjugation (κ := κ) G v g X) := by
  apply continuous_pi
  intro i
  exact (TangentBracket.continuous_matrixConjugation_point G (LocalAdeles.localEmbedding (Sum.inr (v i))) (X i)).comp
    (continuous_apply i)

theorem productMatrixConjugation_mapsTo_tangentCone
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))) (g : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))) :
    MapsTo (productMatrixConjugation (κ := κ) G v g)
      (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) 1)
      (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
        (H.map (MulAut.conj g).toMonoidHom : Set _)) 1) := by
  have he : productMatrixConjugation (κ := κ) G v g '' (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) =
      PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H.map (MulAut.conj g).toMonoidHom : Set _) := by
    rw [Subgroup.coe_map, image_image, image_image]
    rfl
  have ht := TangentCone.continuousLinearMap_mapsTo_tangentCone (productMatrixConjugation (κ := κ) G v g)
    (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) 1
  rw [he, productMatrixConjugation_one] at ht
  exact ht

theorem product_conjugation_preserves_closure_tangentSpan
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))) (g : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))
    (hc : (H.map (MulAut.conj g).toMonoidHom).Commensurable H) :
    MapsTo (productMatrixConjugation (κ := κ) G v g)
      (Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
        (H.topologicalClosure : Set _)) 1) : Set _)
      (Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
        (H.topologicalClosure : Set _)) 1) : Set _) := by
  have ht := productMatrixConjugation_mapsTo_tangentCone (κ := κ) G v H.topologicalClosure g
  rw [← TangentCone.closure_map_conj] at ht
  have hemb : IsEmbedding (PrimeBlockDecomposition.finiteMatrixProductHom G v) :=
    (IsClosedEmbedding.piMap (fun i => IntegralCompact.localPoints_closedEmbedding G (Sum.inr (v i)))).isEmbedding
  have hn := congrArg (Filter.map (PrimeBlockDecomposition.finiteMatrixProductHom G v)) (ClosureCommensurability.commensurable_closures_nhdsWithin_eq hc)
  rw [hemb.map_nhdsWithin_eq, hemb.map_nhdsWithin_eq, map_one] at hn
  have he := tangentConeAt_congr (𝕜 := κ) hn
  let W := Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
    (H.topologicalClosure : Set _)) 1)
  have hle : W ≤ W.comap (productMatrixConjugation (κ := κ) G v g).toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.subset_span (he.le (ht hx))
  exact hle

end

section

/-! The simultaneous tangent commutator limit, over a common scalar
field for the selected local factors. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F κ : Type} [Field F] [NumberField F] [Field κ] {n : ℕ} {ι : Type*}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : ι → HeightOneSpectrum (𝓞 F))
variable [∀ i, Algebra κ ((v i).adicCompletion F)]

theorem scaled_product_conjugation_displacement
    (g : ∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i)))
    (X : ∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)) (c : κ) :
    c • (productMatrixConjugation (κ := κ) G v g X - X) =
      ((c • (PrimeBlockDecomposition.finiteMatrixProductHom G v g - 1)) * X -
        X * (c • (PrimeBlockDecomposition.finiteMatrixProductHom G v g - 1))) * PrimeBlockDecomposition.finiteMatrixProductHom G v g⁻¹ := by
  funext i
  exact TangentBracket.scaled_conjugation_displacement_over (K := (v i).adicCompletion F)
    (κ := κ) G (LocalAdeles.localEmbedding (Sum.inr (v i))) (g i) (X i) c

theorem product_tangent_commutator_mem
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (W : Submodule κ (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)))
    (hclosed : IsClosed (W : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F))))
    (hinvariant : ∀ g ∈ H, MapsTo (productMatrixConjugation (κ := κ) G v g)
      (W : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)))
      (W : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F))))
    {X Y : ∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)}
    (hX : X ∈ W)
    (hY : Y ∈ tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) 1) :
    Y * X - X * Y ∈ W := by
  obtain ⟨α, l, hl, c, d, hd, hs, hcd⟩ := exists_fun_of_mem_tangentConeAt hY
  have hM : Tendsto (fun a => (1 : ∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)) + d a)
      l (𝓝 1) := by simpa only [add_zero] using tendsto_const_nhds.add hd
  let invM := fun a => fun i => ((1 + d a) i).adjugate
  have hi : Tendsto invM l (𝓝 1) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have h := (continuous_id.matrix_adjugate.tendsto
      (1 : Matrix (Fin n) (Fin n) ((v i).adicCompletion F))).comp ((tendsto_pi_nhds.mp hM) i)
    simpa only [invM, Matrix.adjugate_one, Function.comp_def, id_eq, Pi.one_apply] using h
  let z := fun a => ((c a • d a) * X - X * (c a • d a)) * invM a
  have hz : Tendsto z l (𝓝 (Y * X - X * Y)) := by
    simpa only [mul_one] using
      ((hcd.mul tendsto_const_nhds).sub (tendsto_const_nhds.mul hcd)).mul hi
  apply hclosed.mem_of_tendsto hz
  filter_upwards [hs] with a ha
  obtain ⟨g, hg, hge⟩ := ha
  have hm := W.smul_mem (c a) (W.sub_mem (hinvariant g hg hX) hX)
  rw [scaled_product_conjugation_displacement] at hm
  have hginv : PrimeBlockDecomposition.finiteMatrixProductHom G v g⁻¹ = invM a := by
    funext i
    exact congrArg (fun M => (M i).adjugate) hge
  have hdg : PrimeBlockDecomposition.finiteMatrixProductHom G v g - 1 = d a := by
    calc
      PrimeBlockDecomposition.finiteMatrixProductHom G v g - 1 = (1 + d a) - 1 := congrArg (fun M => M - 1) hge
      _ = d a := by abel
  change z a ∈ W
  dsimp only [z]
  simpa only [hdg, hginv] using hm

end

/-! A commensurated simultaneous local subgroup has a tangent ideal in
the tangent Lie algebra of its commensurating group. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set

variable {F κ : Type} [Field F] [NumberField F] [Field κ] {n : ℕ} {ι : Type*}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : ι → HeightOneSpectrum (𝓞 F))
variable [∀ i, Algebra κ ((v i).adicCompletion F)]

theorem product_tangentSpan_commutator_mem
    (H : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (W : Submodule κ (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)))
    (hclosed : IsClosed (W : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F))))
    (hinvariant : ∀ g ∈ H, MapsTo (productMatrixConjugation (κ := κ) G v g)
      (W : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)))
      (W : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F))))
    {X Y : ∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)}
    (hX : X ∈ W)
    (hY : Y ∈ Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) 1)) :
    Y * X - X * Y ∈ W := by
  let f : (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)) →ₗ[κ]
      (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)) := {
    toFun Y := Y * X - X * Y
    map_add' := fun Y Z => by simp only [add_mul, mul_add]; abel
    map_smul' := fun c Y => by
      simp only [smul_mul_assoc, mul_smul_comm, smul_sub, RingHom.id_apply] }
  have hle : Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (H : Set _)) 1) ≤
      W.comap f := by
    apply Submodule.span_le.mpr
    exact fun Y hY => product_tangent_commutator_mem G v H W hclosed hinvariant hX hY
  exact hle hY

theorem product_conjugation_invariance_extends_to_closure
    (R : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (W : Submodule κ (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)))
    (hclosed : IsClosed (W : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F))))
    (hR : ∀ g ∈ R, MapsTo (productMatrixConjugation (κ := κ) G v g)
      (W : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)))
      (W : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)))) :
    ∀ g ∈ R.topologicalClosure, MapsTo (productMatrixConjugation (κ := κ) G v g)
      (W : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)))
      (W : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F))) := by
  intro g hg X hX
  have hs := hclosed.preimage (continuous_productMatrixConjugation_point (κ := κ) G v X)
  exact closure_minimal (fun a ha => hR a ha hX) hs hg

theorem product_tangent_commutator_mem_of_commensurated
    (H R : Subgroup (∀ i, LocalAdeles.LocalPoints G (Sum.inr (v i))))
    (hcomm : ∀ g ∈ R, (H.map (MulAut.conj g).toMonoidHom).Commensurable H)
    (hclosed : IsClosed (Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
      (H.topologicalClosure : Set _)) 1) : Set (∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F))))
    {X Y : ∀ i, Matrix (Fin n) (Fin n) ((v i).adicCompletion F)}
    (hX : X ∈ Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
      (H.topologicalClosure : Set _)) 1))
    (hY : Y ∈ Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
      (R.topologicalClosure : Set _)) 1)) :
    Y * X - X * Y ∈ Submodule.span κ (tangentConeAt κ (PrimeBlockDecomposition.finiteMatrixProductHom G v ''
      (H.topologicalClosure : Set _)) 1) := by
  apply product_tangentSpan_commutator_mem G v R.topologicalClosure _ hclosed _ hX hY
  apply product_conjugation_invariance_extends_to_closure G v R _ hclosed
  exact fun g hg => product_conjugation_preserves_closure_tangentSpan G v H g (hcomm g hg)

end

end OAI.NumberTheory.Quaternion.Arithmetic.ProductTangentTo
