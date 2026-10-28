import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ScalarInverseLimit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham

/-! # Scalar Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ScalarForms.FiniteScalarForms

noncomputable section

/-!
# Coefficient extension of the original completed PD forms

Finite free extension commutes with the compatible-form definition in
every degree and with the actual PD de Rham differential.
-/

open _root_.CategoryTheory Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (A : Type u) [CommRing A] [Algebra k A] (F : ℕᵒᵖ ⥤ PD.Thickening.AffinePDThickening p k A)
  (S : Type u) [CommRing S] [Algebra (WittVector p k) S]

def sourceEquiv (q : ℕ) :
    PD.PDDeRham.CompletedForm p k A F q ≃ₗ[WittVector p k]
      Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible (WittVector p k) (PD.PDDeRham.Form p k A F q)
        (PD.PDDeRham.transition p k A F q) where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev Form (q : ℕ) :=
  ScalarInverseLimit.FiniteScalarInverseLimit.compatible (WittVector p k) S (PD.PDDeRham.Form p k A F q)
    (PD.PDDeRham.transition p k A F q)

def levelDifferential (q i : ℕ) :
    PD.PDDeRham.Form p k A F q i →ₗ[WittVector p k]
      PD.PDDeRham.Form p k A F (q + 1) i :=
  PD.DeRham.PDDeRham.differential (WittVector p k) (F.obj (op i)).ring
    (RingHom.ker (F.obj (op i)).reduction) (F.obj (op i)).dividedPowers q

def differential (q : ℕ) : Form p k A F S q →ₗ[S] Form p k A F S (q + 1) :=
  Cohomology.Module.InverseLimit.ModuleInverseLimit.map S
    (fun i => S ⊗[WittVector p k] PD.PDDeRham.Form p k A F q i)
    (ScalarInverseLimit.FiniteScalarInverseLimit.transition (WittVector p k) S
      (PD.PDDeRham.Form p k A F q) (PD.PDDeRham.transition p k A F q))
    (fun i => S ⊗[WittVector p k] PD.PDDeRham.Form p k A F (q + 1) i)
    (ScalarInverseLimit.FiniteScalarInverseLimit.transition (WittVector p k) S
      (PD.PDDeRham.Form p k A F (q + 1)) (PD.PDDeRham.transition p k A F (q + 1)))
    (fun i => (levelDifferential p k A F q i).baseChange S) (by
      intro n m h z
      induction z using TensorProduct.inductionOn with
      | tmul s x =>
          exact congrArg (fun y => s ⊗ₜ[WittVector p k] y)
            (PD.PDDeRham.transition_differential p k A F q n m h x).symm
      | add x y hx hy => simp only [map_add, hx, hy])

variable (ξ : Type u) [Fintype ξ] (b : Module.Basis ξ (WittVector p k) S)

def equiv (q : ℕ) :
    S ⊗[WittVector p k] PD.PDDeRham.CompletedForm p k A F q ≃ₗ[S] Form p k A F S q :=
  (LinearEquiv.baseChange (WittVector p k) S _ _ (sourceEquiv p k A F q)).trans
    (ScalarInverseLimit.FiniteScalarInverseLimit.equiv (WittVector p k) S (PD.PDDeRham.Form p k A F q)
      (PD.PDDeRham.transition p k A F q) ξ b)

theorem equiv_eval (q i : ℕ)
    (z : S ⊗[WittVector p k] PD.PDDeRham.CompletedForm p k A F q) :
    (equiv p k A F S ξ b q z).val i = (PD.PDDeRham.eval p k A F q i).baseChange S z := by
  have he := ScalarInverseLimit.FiniteScalarInverseLimit.equiv_eval (WittVector p k) S
    (PD.PDDeRham.Form p k A F q) (PD.PDDeRham.transition p k A F q) ξ b i
    (LinearEquiv.baseChange (WittVector p k) S _ _ (sourceEquiv p k A F q) z)
  refine he.trans ?_
  clear he
  induction z using TensorProduct.inductionOn with
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem equiv_differential (q : ℕ)
    (z : S ⊗[WittVector p k] PD.PDDeRham.CompletedForm p k A F q) :
    equiv p k A F S ξ b (q + 1) ((PD.PDDeRham.differential p k A F q).baseChange S z) =
      differential p k A F S q (equiv p k A F S ξ b q z) := by
  apply Subtype.ext
  funext i
  change (equiv p k A F S ξ b (q + 1)
    ((PD.PDDeRham.differential p k A F q).baseChange S z)).val i =
      (levelDifferential p k A F q i).baseChange S ((equiv p k A F S ξ b q z).val i)
  rw [equiv_eval, equiv_eval]
  induction z using TensorProduct.inductionOn with
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ScalarForms.FiniteScalarForms
