import OAI.NumberTheory.Quaternion.Arithmetic.LocalSubgroup
import OAI.NumberTheory.Quaternion.Arithmetic.LocalCompletion

/-! # Matrix Openness -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MatrixOpenness

noncomputable section

/-! A closed subgroup of local algebraic matrix points is open when its
prime-field tangent span equals the tangent span of the full local group.
This is a proved local criterion, with no openness assumption. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Operator
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def localMatrixMonoidHom (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (v : HeightOneSpectrum (𝓞 F)) :
    LocalAdeles.LocalPoints G (Sum.inr v) →* Matrix (Fin n) (Fin n) (v.adicCompletion F) where
  toFun g := (g.val : Matrix (Fin n) (Fin n) (LocalAdeles.Completion (Sum.inr v)))
  map_one' := rfl
  map_mul' _ _ := rfl

theorem local_subgroup_isOpen_of_tangentSpan_eq (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : HeightOneSpectrum (𝓞 F)) (H : Subgroup (LocalAdeles.LocalPoints G (Sum.inr v)))
    (hH : IsClosed (H : Set (LocalAdeles.LocalPoints G (Sum.inr v))))
    (hspan : TangentBracket.matrixTangentSpanOver (K := v.adicCompletion F)
      (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F))
      G (LocalAdeles.localEmbedding (Sum.inr v)) H =
      TangentBracket.matrixTangentSpanOver (K := v.adicCompletion F)
        (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F))
        G (LocalAdeles.localEmbedding (Sum.inr v)) ⊤) :
    IsOpen (H : Set (LocalAdeles.LocalPoints G (Sum.inr v))) := by
  let : NontriviallyNormedField (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) :=
    TangentBracket.finiteClosedPrimeNontriviallyNormedField v
  let : FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) :=
    LocalCompletion.finiteCompletion_finiteDimensional_closedPrime v
  let : @CompleteSpace (Matrix (Fin n) (Fin n) (v.adicCompletion F))
      (inferInstance : NormedRing (Matrix (Fin n) (Fin n) (v.adicCompletion F))).toUniformSpace := by
    apply FiniteDimensional.complete (v.adicCompletion F)
  let e := localMatrixMonoidHom G v
  let HM := H.toSubmonoid.map e
  let GM := (⊤ : Subgroup (LocalAdeles.LocalPoints G (Sum.inr v))).toSubmonoid.map e
  have hemb : IsClosedEmbedding e := IntegralCompact.localPoints_closedEmbedding G (Sum.inr v)
  have hHM : IsClosed (HM : Set (Matrix (Fin n) (Fin n) (v.adicCompletion F))) :=
    hemb.isClosedMap _ hH
  have hs : LocalSubgroup.primeLocalTangentSpan v GM ≤ LocalSubgroup.primeLocalTangentSpan v HM := by
    change TangentBracket.matrixTangentSpanOver (K := v.adicCompletion F)
        (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F))
        G (LocalAdeles.localEmbedding (Sum.inr v)) ⊤ ≤
      TangentBracket.matrixTangentSpanOver (K := v.adicCompletion F)
        (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F))
        G (LocalAdeles.localEmbedding (Sum.inr v)) H
    exact hspan.symm.le
  have hm := LocalSubgroup.tangentSpan_le_implies_local_containment v HM GM hHM hs
  have hecont := hemb.continuous.tendsto (1 : LocalAdeles.LocalPoints G (Sum.inr v))
  rw [map_one] at hecont
  have hpull := hecont hm
  apply H.isOpen_of_mem_nhds (g := 1)
  filter_upwards [hpull] with g hg
  have hgm : e g ∈ GM := ⟨g, by trivial, rfl⟩
  obtain ⟨a, ha, he⟩ := hg hgm
  exact hemb.injective he ▸ ha

end

end OAI.NumberTheory.Quaternion.Arithmetic.MatrixOpenness
