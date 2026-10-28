import OAI.ArithmeticGeometry.Descent.CMVariety.OverEndomorphism

/-! # Finite Coefficient Tuples -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientTuples.Abelian

noncomputable section

section

/-! Simultaneous finite-coefficient descent for finite tuples of actual maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

theorem finite_scheme_morphisms_descend_to_finite_coefficients
    {Index : Type} [Fintype Index] {Y X : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation g]
    (a : Index → (pullback (Spec.map (CommRingCat.ofHom (algebraMap R B))) f ⟶ X))
    (ha : ∀ i, a i ≫ g = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) f ≫ f) :
    ∃ (s : (Finset B)ᵒᵖ)
      (k : Index → ((FiniteCoefficientFst.Abelian.finiteCoefficientFamilyDiagram R B f).obj s ⟶ X)),
      ∀ i, (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B f).π.app s ≫ k i = a i ∧
        k i ≫ g = (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyStructure R B f).app s ≫ f := by
  choose stage k hk hkg using fun i =>
    FiniteCoefficientFst.Abelian.scheme_morphism_descends_to_finite_coefficients R B f g (a i) (ha i)
  let s : Finset B := Finset.univ.biUnion (fun i => (stage i).unop)
  have hle (i : Index) : (stage i).unop ⊆ s :=
    Finset.subset_biUnion_of_mem (fun j => (stage j).unop) (Finset.mem_univ i)
  let j (i : Index) : Opposite.op s ⟶ stage i := (homOfLE (hle i)).op
  let D := FiniteCoefficientFst.Abelian.finiteCoefficientFamilyDiagram R B f
  let p := FiniteCoefficientFst.Abelian.finiteCoefficientFamilyStructure R B f
  let c := FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B f
  refine ⟨.op s, fun i => D.map (j i) ≫ k i, fun i => ⟨?_, ?_⟩⟩
  · change c.π.app (.op s) ≫ (D.map (j i) ≫ k i) = a i
    rw [← Category.assoc, c.w (j i)]
    exact hk i
  · have hp : D.map (j i) ≫ p.app (stage i) = p.app (.op s) :=
      (p.naturality (j i)).trans (Category.comp_id _)
    change (D.map (j i) ≫ k i) ≫ g = p.app (.op s) ≫ f
    rw [Category.assoc, hkg i, ← Category.assoc, hp]

theorem finite_scheme_endomorphisms_descend_to_finite_coefficients
    {Index : Type} [Fintype Index] {Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation f]
    (k : Index → (pullback (Spec.map (CommRingCat.ofHom (algebraMap R B))) f ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R B))) f))
    (hk : ∀ i, k i ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B))) f =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R B))) f) :
    ∃ (s : (Finset B)ᵒᵖ)
      (e : Index → (pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f ⟶
        pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f)),
      ∀ i, e i ≫ pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f =
        pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f ∧
      (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B f).π.app s ≫ e i =
        k i ≫ (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B f).π.app s := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hbase (i : Index) : (k i ≫ pullback.snd p f) ≫ f = pullback.snd p f ≫ f := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hk i, pullback.condition]
  obtain ⟨s, a, ha⟩ := finite_scheme_morphisms_descend_to_finite_coefficients R B f f
    (fun i => k i ≫ pullback.snd p f) hbase
  let a' : Index → (pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f ⟶ Y) := a
  let q : pullback p f ⟶ pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f :=
    (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B f).π.app s
  have hqfst : q ≫ pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f =
      pullback.fst p f ≫ Spec.map
        (CommRingCat.ofHom (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop).val.toRingHom) :=
    FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone_fst R B f s
  have hqsnd : q ≫ pullback.snd (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f = pullback.snd p f :=
    FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone_structure R B f s
  have hpair (i : Index) : pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f ≫
      FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop = a' i ≫ f :=
    (pullback.condition).trans (ha i).2.symm
  let e (i : Index) :=
    pullback.lift (pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) f) (a' i) (hpair i)
  refine ⟨s, e, fun i => ⟨pullback.lift_fst _ _ _, ?_⟩⟩
  change q ≫ e i = k i ≫ q
  dsimp only [e]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, hqfst,
      ← Category.assoc, hk i]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, hqsnd]
    exact (ha i).1

end

/-! A finite tuple descends in the actual over category at one common stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical

theorem finite_over_endomorphisms_descend_to_finite_coefficients
    (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    {Index : Type} [Fintype Index] (A : Over (Spec (CommRingCat.of R)))
    [QuasiCompact A.hom] [QuasiSeparated A.hom] [LocallyOfFinitePresentation A.hom]
    (k : Index → ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj A)) :
    ∃ (s : (Finset B)ᵒᵖ)
      (a : Index → ((Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).obj A ⟶
        (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).obj A)),
      ∀ i, OverEndomorphism.Abelian.standardCoefficientProjection R B A s ≫ (a i).left =
        (k i).left ≫ OverEndomorphism.Abelian.standardCoefficientProjection R B A s := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let e := pullbackSymmetry A.hom p
  let k' : Index → (pullback A.hom p ⟶ pullback A.hom p) := fun i => (k i).left
  have hkw (i : Index) : k' i ≫ pullback.snd A.hom p = pullback.snd A.hom p := (k i).w
  let u (i : Index) := e.inv ≫ k' i ≫ e.hom
  have hu (i : Index) : u i ≫ pullback.fst p A.hom = pullback.fst p A.hom := by
    dsimp only [u, e]
    rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst,
      hkw i, pullbackSymmetry_inv_comp_snd]
  obtain ⟨s, a, ha⟩ := finite_scheme_endomorphisms_descend_to_finite_coefficients R B A.hom u hu
  let d := pullbackSymmetry A.hom (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)
  have hw (i : Index) : (d.hom ≫ a i ≫ d.inv) ≫
      pullback.snd A.hom (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) =
        pullback.snd A.hom (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) := by
    dsimp only [d]
    rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_snd,
      (ha i).1, pullbackSymmetry_hom_comp_fst]
  let a' (i : Index) : (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).obj A ⟶
      (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).obj A :=
    Over.homMk (d.hom ≫ a i ≫ d.inv) (hw i)
  refine ⟨s, a', fun i => ?_⟩
  exact OverEndomorphism.Abelian.iso_conjugate_commuting_square e d ((FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B A.hom).π.app s)
    (k' i) (a i) (ha i).2

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientTuples.Abelian
