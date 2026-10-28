import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdicModules
import Mathlib.RingTheory.Finiteness.Basic

/-! # Adic Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdicFiniteness

noncomputable section

/-! A separated module with finite residue is finitely generated over a principal-adically complete ring. -/

universe u v

variable (R : Type u) [CommRing R] (r : R) [IsPrecomplete (Ideal.span {r}) R]
  (M : Type v) [AddCommGroup M] [Module R M] [IsHausdorff (Ideal.span {r}) M]

theorem finite [Finite (M ⧸ ((Ideal.span {r}) • (⊤ : Submodule R M)))] : Module.Finite R M := by
  classical
  let P : Submodule R M := (Ideal.span {r}) • ⊤
  let Q := M ⧸ P
  let : Fintype Q := Fintype.ofFinite Q
  let v (q : Q) : M := (P.mkQ_surjective q).choose
  have hv (q : Q) : P.mkQ (v q) = q := (P.mkQ_surjective q).choose_spec
  let f : (Q → R) →ₗ[R] M := LinearMap.lsum R (fun _ : Q => R) R
    (fun q => LinearMap.toSpanSingleton R M (v q))
  let : IsPrecomplete (Ideal.span {r}) (Q → R) :=
    AdicModules.pi_precomplete R r (fun _ : Q => R)
  apply Module.Finite.of_surjective f
  apply surjective_of_mkQ_comp_surjective (I := Ideal.span {r})
  intro q
  refine ⟨Pi.single q 1, ?_⟩
  change P.mkQ (f (Pi.single q 1)) = q
  have h : f (Pi.single q 1) = v q := by
    dsimp only [f]
    rw [LinearMap.lsum_piSingle]
    exact one_smul R (v q)
  exact (congrArg P.mkQ h).trans (hv q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.AdicFiniteness
