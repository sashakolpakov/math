import OAI.NumberTheory.Quaternion.Arithmetic.TangentScalarEquivalence
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeField
import OAI.NumberTheory.Quaternion.Arithmetic.LocalTangent

/-! # Prime Block Local Tangent -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockLocalTangent

noncomputable section

/-! Each factor's full local tangent span remains its infinitesimal Lie
algebra when viewed over the common prime field of its residue block. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain

attribute [local instance] LieRing.ofAssociativeRing

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem primeBlock_local_tangentSpan_eq_infinitesimal (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (hG : G.IsGeometricallyConnected) (v w : HeightOneSpectrum (𝓞 F))
    (hvw : LocalCompletion.residuePrime v = LocalCompletion.residuePrime w) :
    letI := PrimeField.primeBlockScalarAlgebra v w hvw
    TangentBracket.matrixTangentSpanOver (K := w.adicCompletion F) (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F))
      G (LocalAdeles.localEmbedding (Sum.inr w)) ⊤ =
      (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange (K := w.adicCompletion F)
        G (LocalAdeles.localEmbedding (Sum.inr w)))).toSubmodule.restrictScalars
          (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) := by
  let : Algebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (w.adicCompletion F) :=
    PrimeField.primeBlockScalarAlgebra v w hvw
  let κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F)
  let κw := TangentBracket.closedPrimeSubfield (w.adicCompletion F)
  let : Algebra κ κw := (PrimeField.closedPrimeFieldMap v w hvw).toAlgebra
  let : IsScalarTower κ κw (w.adicCompletion F) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hs := TangentScalarEquivalence.tangentSpan_eq_restrictScalars_of_surjective
    (E := Matrix (Fin n) (Fin n) (w.adicCompletion F))
    (κ := κ) (κ' := κw) (PrimeField.closedPrimeFieldRingEquiv v w hvw).surjective
    (MatrixOpenness.localMatrixMonoidHom G w '' Set.univ) 1
  have he : TangentBracket.matrixTangentSpanOver (K := w.adicCompletion F) (κ := κ)
      G (LocalAdeles.localEmbedding (Sum.inr w)) ⊤ =
      (TangentBracket.matrixTangentSpanOver (K := w.adicCompletion F) (κ := κw)
        G (LocalAdeles.localEmbedding (Sum.inr w)) ⊤).restrictScalars κ := hs
  rw [LocalTangent.finite_prime_tangentSpan_eq_infinitesimal G hG w] at he
  exact he

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockLocalTangent
