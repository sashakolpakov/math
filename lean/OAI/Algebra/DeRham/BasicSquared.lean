/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
This file has been modified.
-/
import OAI.Algebra.DeRham.Basic

/-! # Basic Squared -/

namespace OAI.Algebra.DeRham.BasicSquared

noncomputable section

open _root_.Algebra

/-!
# Algebraic de Rham forms

-/

universe u

open CliffordAlgebra (involute involute_ι)
open TrivSqZeroExt (snd)

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

variable {R A}

variable (R A)

/-- The exterior derivative anticommutes with the grade involution, since it raises the degree
by one. -/
lemma extDeriv_involute (x : Basic.ExtAlg R A) :
    Basic.extDeriv R A (involute x) = -involute (Basic.extDeriv R A x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp
  | ι ω => simp [Basic.involute_snd_phi]
  | mul x y hx hy =>
      rw [map_mul, Basic.extDeriv_mul, hx, hy, Basic.extDeriv_mul, map_add, map_mul, map_mul,
        CliffordAlgebra.involute_involute]
      simp only [mul_neg, neg_mul, neg_add]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

lemma extDeriv_snd_phi (ω : Ω[A⁄R]) : Basic.extDeriv R A (snd (Basic.phi R A ω)) = 0 := by
  induction ω using Basic.D_induction with
  | D a => simp
  | zero => simp
  | add x y hx hy => rw [map_add, TrivSqZeroExt.snd_add, map_add, hx, hy, add_zero]
  | smul a x hx =>
      rw [Basic.snd_phi_smul, map_add, Algebra.smul_def, Basic.extDeriv_mul, Basic.extDeriv_mul, hx,
        AlgHom.commutes, Basic.extDeriv_algebraMap, mul_zero, zero_add, involute_ι]
      simp only [Basic.extDeriv_ι, Basic.phi_D, TrivSqZeroExt.snd_inl, zero_mul, add_zero, neg_mul]
      abel

/-- The exterior derivative squares to zero. -/
lemma extDeriv_extDeriv (x : Basic.ExtAlg R A) : Basic.extDeriv R A (Basic.extDeriv R A x) = 0 := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp
  | ι ω => rw [Basic.extDeriv_ι]; exact extDeriv_snd_phi R A ω
  | mul x y hx hy =>
      rw [Basic.extDeriv_mul, map_add, Basic.extDeriv_mul, Basic.extDeriv_mul, hx, hy, extDeriv_involute,
        CliffordAlgebra.involute_involute]
      simp only [mul_zero, zero_mul, neg_mul, zero_add, add_zero, neg_add_cancel]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

lemma differential_squared (p : ℕ) (x : Basic.Form R A p) :
    Basic.differential R A (p + 1) (Basic.differential R A p x) = 0 :=
  Subtype.ext (extDeriv_extDeriv R A x)

/-! ### Functoriality -/

section Tower

variable (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

lemma extAlgMap_involute (x : Basic.ExtAlg R A) :
    Basic.extAlgMap R A B (involute x) = involute (Basic.extAlgMap R A B x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => simp
  | ι ω => simp
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma extAlgMap_snd_phi (ω : Ω[A⁄R]) :
    Basic.extAlgMap R A B (snd (Basic.phi R A ω)) =
      snd (Basic.phi R B (KaehlerDifferential.map R R A B ω)) := by
  induction ω using Basic.D_induction with
  | D a => simp
  | zero => simp
  | add x y hx hy => simp only [map_add, Basic.Sq.snd_add, hx, hy]
  | smul a x hx =>
      rw [Basic.snd_phi_smul, map_add, map_smul, hx, map_mul, Basic.extAlgMap_ι, Basic.extAlgMap_ι,
        KaehlerDifferential.map_D, map_smul,
        ← algebraMap_smul (R := A) B a (KaehlerDifferential.map R R A B x), Basic.snd_phi_smul,
        ← algebraMap_smul (R := A) B a (snd (Basic.phi R B (KaehlerDifferential.map R R A B x)))]

lemma extAlgMap_extDeriv (x : Basic.ExtAlg R A) :
    Basic.extAlgMap R A B (Basic.extDeriv R A x) = Basic.extDeriv R B (Basic.extAlgMap R A B x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a =>
      rw [Basic.extDeriv_algebraMap, Basic.extAlgMap_ι, KaehlerDifferential.map_D, Basic.extAlgMap_algebraMap,
        Basic.extDeriv_algebraMap]
  | ι ω => rw [Basic.extDeriv_ι, extAlgMap_snd_phi, Basic.extAlgMap_ι, Basic.extDeriv_ι]
  | mul x y hx hy =>
      rw [Basic.extDeriv_mul, map_add, map_mul, map_mul, hx, hy, extAlgMap_involute, map_mul,
        Basic.extDeriv_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tower

variable {A}
variable {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

lemma map_differential (f : A →ₐ[R] B) (p : ℕ) (x : Basic.Form R A p) :
    Basic.map R f (p + 1) (Basic.differential R A p x) = Basic.differential R B p (Basic.map R f p x) := by
  let _ := f.toAlgebra
  exact Subtype.ext (extAlgMap_extDeriv R A B x)

end

end OAI.Algebra.DeRham.BasicSquared
