import OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst

/-! # Finite Coefficient Equalities -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientEqualities.Abelian

noncomputable section

/-!
Equalities between actual family morphisms that hold over the coefficient
algebra already hold after adjoining finitely many coefficients. These are
the algebraic equations needed to descend the group-homomorphism laws.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

theorem family_morphism_equality_descends_to_finite_coefficients
    {Y X : Scheme} (f : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType g]
    (a b : Y ⟶ X) (ha : a ≫ g = f) (hb : b ≫ g = f)
    (hB : pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) f ≫ a =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) f ≫ b) :
    ∃ s : (Finset B)ᵒᵖ,
      (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyStructure R B f).app s ≫ a =
        (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyStructure R B f).app s ≫ b := by
  let s₀ : (Finset B)ᵒᵖ := .op ∅
  let D := FiniteCoefficientFst.Abelian.finiteCoefficientFamilyDiagram R B f
  let p := FiniteCoefficientFst.Abelian.finiteCoefficientFamilyStructure R B f
  let c := FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B f
  have h₀ : c.π.app s₀ ≫ (p.app s₀ ≫ a) = c.π.app s₀ ≫ (p.app s₀ ≫ b) := by
    rw [← Category.assoc, ← Category.assoc]
    change ((FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B f).π.app s₀ ≫
      (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyStructure R B f).app s₀) ≫ a = _
    rw [FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone_structure]
    exact hB
  obtain ⟨s, i, heq⟩ := FiniteCoefficientFst.Abelian.scheme_morphism_equality_descends_to_finite_coefficients R B f g s₀
    (p.app s₀ ≫ a) (p.app s₀ ≫ b)
    (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb]) h₀
  have hp : D.map i ≫ p.app s₀ = p.app s :=
    (p.naturality i).trans (Category.comp_id _)
  refine ⟨s, ?_⟩
  change D.map i ≫ (p.app s₀ ≫ a) = D.map i ≫ (p.app s₀ ≫ b) at heq
  rw [← Category.assoc, ← Category.assoc, hp] at heq
  exact heq

theorem finite_family_morphism_equalities_descend
    {Index : Type} [Fintype Index] (Y X : Index → Scheme)
    (f : ∀ i, Y i ⟶ Spec (CommRingCat.of R)) [∀ i, QuasiCompact (f i)]
    (g : ∀ i, X i ⟶ Spec (CommRingCat.of R)) [∀ i, LocallyOfFiniteType (g i)]
    (a b : ∀ i, Y i ⟶ X i) (ha : ∀ i, a i ≫ g i = f i) (hb : ∀ i, b i ≫ g i = f i)
    (hB : ∀ i, pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (f i) ≫ a i =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) (f i) ≫ b i) :
    ∃ s : (Finset B)ᵒᵖ, ∀ i,
      (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyStructure R B (f i)).app s ≫ a i =
        (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyStructure R B (f i)).app s ≫ b i := by
  choose stage hstage using fun i =>
    family_morphism_equality_descends_to_finite_coefficients R B (f i) (g i)
      (a i) (b i) (ha i) (hb i) (hB i)
  let s : Finset B := Finset.univ.biUnion (fun i => (stage i).unop)
  have hle (i : Index) : (stage i).unop ⊆ s :=
    Finset.subset_biUnion_of_mem (fun j => (stage j).unop) (Finset.mem_univ i)
  refine ⟨.op s, fun i => ?_⟩
  let j : Opposite.op s ⟶ stage i := (homOfLE (hle i)).op
  let D := FiniteCoefficientFst.Abelian.finiteCoefficientFamilyDiagram R B (f i)
  let p := FiniteCoefficientFst.Abelian.finiteCoefficientFamilyStructure R B (f i)
  have hp : D.map j ≫ p.app (stage i) = p.app (.op s) :=
    (p.naturality j).trans (Category.comp_id _)
  have h := congrArg (fun u => D.map j ≫ u) (hstage i)
  change D.map j ≫ (p.app (stage i) ≫ a i) = D.map j ≫ (p.app (stage i) ≫ b i) at h
  rw [← Category.assoc, ← Category.assoc, hp] at h
  exact h

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientEqualities.Abelian
