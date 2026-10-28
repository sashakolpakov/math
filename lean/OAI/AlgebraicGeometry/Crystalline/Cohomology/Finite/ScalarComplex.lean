import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ScalarForms

/-! # Scalar Complex -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ScalarComplex.FiniteScalarComplex

noncomputable section

/-!
# Finite coefficient extension commutes with the completed PD complex

Both complexes use the original PD de Rham differential: one extends
the completed forms, and the other takes compatible extended forms.
-/

open _root_.CategoryTheory Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (A : Type u) [CommRing A] [Algebra k A] (F : ℕᵒᵖ ⥤ PD.Thickening.AffinePDThickening p k A)
  (S : Type u) [CommRing S] [Algebra (WittVector p k) S]

theorem source_square (q : ℕ)
    (z : S ⊗[WittVector p k] PD.PDDeRham.CompletedForm p k A F q) :
    (PD.PDDeRham.differential p k A F (q + 1)).baseChange S
      ((PD.PDDeRham.differential p k A F q).baseChange S z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
      change s ⊗ₜ[WittVector p k]
        (PD.PDDeRham.differential p k A F (q + 1)
          (PD.PDDeRham.differential p k A F q x)) = 0
      rw [PD.PDDeRham.differential_square, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem target_square (q : ℕ) (x : ScalarForms.FiniteScalarForms.Form p k A F S q) :
    ScalarForms.FiniteScalarForms.differential p k A F S (q + 1)
      (ScalarForms.FiniteScalarForms.differential p k A F S q x) = 0 := by
  apply Subtype.ext
  funext i
  change (ScalarForms.FiniteScalarForms.levelDifferential p k A F (q + 1) i).baseChange S
    ((ScalarForms.FiniteScalarForms.levelDifferential p k A F q i).baseChange S (x.val i)) = 0
  generalize x.val i = z
  induction z using TensorProduct.inductionOn with
  | tmul s a =>
      change s ⊗ₜ[WittVector p k]
        (PD.DeRham.PDDeRham.differential (WittVector p k) (F.obj (op i)).ring
          (RingHom.ker (F.obj (op i)).reduction) (F.obj (op i)).dividedPowers (q + 1)
          (PD.DeRham.PDDeRham.differential (WittVector p k) (F.obj (op i)).ring
            (RingHom.ker (F.obj (op i)).reduction) (F.obj (op i)).dividedPowers q a)) = 0
      rw [PD.DeRham.PDDeRham.differential_square, TensorProduct.tmul_zero]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

def source : CochainComplex (ModuleCat.{u} S) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of S (S ⊗[WittVector p k] PD.PDDeRham.CompletedForm p k A F q))
    (fun q => ModuleCat.ofHom ((PD.PDDeRham.differential p k A F q).baseChange S))
    (fun q => ModuleCat.hom_ext (LinearMap.ext (source_square p k A F S q)))

def target : CochainComplex (ModuleCat.{u} S) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of S (ScalarForms.FiniteScalarForms.Form p k A F S q))
    (fun q => ModuleCat.ofHom (ScalarForms.FiniteScalarForms.differential p k A F S q))
    (fun q => ModuleCat.hom_ext (LinearMap.ext (target_square p k A F S q)))

variable (ξ : Type u) [Fintype ξ] (b : Module.Basis ξ (WittVector p k) S)

def componentIso (q : ℕ) : (source p k A F S).X q ≅ (target p k A F S).X q :=
  (ScalarForms.FiniteScalarForms.equiv p k A F S ξ b q).toModuleIso

def iso : source p k A F S ≅ target p k A F S :=
  HomologicalComplex.Hom.isoOfComponents (componentIso p k A F S ξ b) (by
    intro q r h
    change q + 1 = r at h
    subst r
    dsimp only [source, target]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun z => (ScalarForms.FiniteScalarForms.equiv_differential p k A F S ξ b q z).symm))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.ScalarComplex.FiniteScalarComplex
