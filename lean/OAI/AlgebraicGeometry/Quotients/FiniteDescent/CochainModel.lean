import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainCompletion
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CohomologyCokernel

/-! # Cochain Model -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainModel

noncomputable section

/-! A bounded-complex model with finite free positive terms and a flat first term. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.CochainFiniteModel

variable {R : Type u} [CommRing R]

structure Model (C : CochainComplex (ModuleCat.{u} R) ℕ) where
  complex : CochainComplex (ModuleCat.{u} R) ℕ
  comparison : complex ⟶ C
  quasiIso : QuasiIso comparison
  flat : ∀ n, Module.Flat R (complex.X n)
  finite : ∀ n, Module.Finite R (complex.X (n + 1))
  free : ∀ n, Module.Free R (complex.X (n + 1))
  bounded : ∃ N, ∀ q, N ≤ q → IsZero (complex.X q)
  tensor_quasiIso : ∀ (A : Type u) [AddCommGroup A] [Module R A],
    QuasiIso (ModuleTensor.Construction.ModuleTensorFunctor.map A comparison)

variable [IsNoetherianRing R]

def improve {C E : CochainComplex (ModuleCat.{u} R) ℕ} (φ : E ⟶ C)
    [QuasiIso φ] [Module.Finite R (C.homology 1)]
    (hflat : ∀ n, Module.Flat R (E.X n))
    (hfinite : ∀ n, Module.Finite R (E.X (n + 2)))
    (hfree : ∀ n, Module.Free R (E.X (n + 2)))
    (hbound : ∃ N, ∀ q, N ≤ q → IsZero (E.X q))
    (htensor : ∀ (A : Type u) [AddCommGroup A] [Module R A],
      QuasiIso (ModuleTensor.Construction.ModuleTensorFunctor.map A φ)) : Model C := by
  have : Module.Finite R (E.homology 1) :=
    Module.Finite.equiv (isoOfQuasiIsoAt φ 1).symm.toLinearEquiv
  have : Module.Finite R (E.sc' 0 1 2).homology :=
    Module.Finite.equiv (E.homologyIsoSc' 0 1 2 (by simp) (by simp)).toLinearEquiv
  have : Module.Finite R (E.sc' 0 1 2).X₃ := hfinite 0
  have : Module.Finite R (E.X 1 ⧸ (E.d 0 1).hom.range) :=
    CohomologyCokernel.Construction.FiniteCohomologyCokernel.finite_cokernel (E.sc' 0 1 2)
  let V := FreeCokernel.Construction.FiniteFreeCokernel.completion (E.d 0 1).hom
  have : Module.Flat R (E.X 0) := hflat 0
  have : Module.Flat R (E.X 1) := hflat 1
  have : QuasiIso (CochainHeadOne.Construction.CochainHeadCompletion.comparison E V.generators) :=
    CochainHeadOne.Construction.CochainHeadCompletion.quasiIso E V.generators V.surjective
  refine {
    complex := CochainHeadOne.Construction.CochainHeadCompletion.complex E V.generators
    comparison := CochainHeadOne.Construction.CochainHeadCompletion.comparison E V.generators ≫ φ
    quasiIso := inferInstance
    flat := ?_
    finite := ?_
    free := ?_
    bounded := ?_
    tensor_quasiIso := ?_ }
  · intro n
    rcases n with _ | _ | n
    · exact V.flat_kernel
    · exact inferInstanceAs (Module.Flat R (Fin V.n → R))
    · exact hflat (n + 2)
  · intro n
    cases n with
    | zero => exact inferInstanceAs (Module.Finite R (Fin V.n → R))
    | succ n => exact hfinite n
  · intro n
    cases n with
    | zero => exact inferInstanceAs (Module.Free R (Fin V.n → R))
    | succ n => exact hfree n
  · obtain ⟨N, hN⟩ := hbound
    refine ⟨N + 2, fun q hq => ?_⟩
    rcases q with _ | _ | q
    · omega
    · omega
    · exact hN (q + 2) (by omega)
  · intro A _ _
    have := htensor A
    have := CochainCompletion.Construction.CochainCompletionTensor.quasiIso E V.generators A V.surjective
    change QuasiIso (((ModuleTensor.Construction.ModuleTensorFunctor.tensor A).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (CochainHeadOne.Construction.CochainHeadCompletion.comparison E V.generators ≫ φ))
    rw [Functor.map_comp]
    infer_instance

end Construction.CochainFiniteModel

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainModel
