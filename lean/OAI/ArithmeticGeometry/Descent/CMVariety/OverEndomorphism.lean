import OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst

/-! # Over Endomorphism -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.OverEndomorphism.Abelian

noncomputable section

/-!
Reconcile the coefficient-family pullback with the literal pullback used
by abelian schemes. Actual endomorphisms then descend as morphisms in the
over category, with an exact comparison to the original endomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical

theorem iso_conjugate_commuting_square
    {C : Type*} [Category* C] {X X' Y Y' : C}
    (e : X ≅ X') (d : Y ≅ Y') (q : X' ⟶ Y') (k : X ⟶ X) (u : Y' ⟶ Y')
    (h : q ≫ u = (e.inv ≫ k ≫ e.hom) ≫ q) :
    (e.hom ≫ q ≫ d.inv) ≫ (d.hom ≫ u ≫ d.inv) = k ≫ (e.hom ≫ q ≫ d.inv) := by
  simp only [Category.assoc, d.inv_hom_id_assoc]
  rw [← Category.assoc q u d.inv, h]
  simp only [Category.assoc, e.hom_inv_id_assoc]

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def standardCoefficientProjection
    (A : Over (Spec (CommRingCat.of R))) (s : (Finset B)ᵒᵖ) :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj A).left ⟶
      ((Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).obj A).left :=
  (pullbackSymmetry A.hom (Spec.map (CommRingCat.ofHom (algebraMap R B)))).hom ≫
    (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B A.hom).π.app s ≫
      (pullbackSymmetry A.hom (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).inv

theorem standardCoefficientProjection_fst
    (A : Over (Spec (CommRingCat.of R))) (s : (Finset B)ᵒᵖ) :
    standardCoefficientProjection R B A s ≫
      pullback.fst A.hom (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) =
        pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let q : pullback p A.hom ⟶ pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) A.hom :=
    (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B A.hom).π.app s
  have hq : q ≫ pullback.snd (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) A.hom = pullback.snd p A.hom :=
    FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone_structure R B A.hom s
  change ((pullbackSymmetry A.hom p).hom ≫ q ≫
    (pullbackSymmetry A.hom (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).inv) ≫ _ = _
  rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_fst,
    hq, pullbackSymmetry_hom_comp_snd]

theorem standardCoefficientProjection_snd
    (A : Over (Spec (CommRingCat.of R))) (s : (Finset B)ᵒᵖ) :
    standardCoefficientProjection R B A s ≫
      pullback.snd A.hom (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) =
        pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap R B))) ≫
          Spec.map (CommRingCat.ofHom (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop).val.toRingHom) := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let q : pullback p A.hom ⟶ pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) A.hom :=
    (FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B A.hom).π.app s
  have hq : q ≫ pullback.fst (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) A.hom = pullback.fst p A.hom ≫
      Spec.map (CommRingCat.ofHom (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop).val.toRingHom) :=
    FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone_fst R B A.hom s
  change ((pullbackSymmetry A.hom p).hom ≫ q ≫
    (pullbackSymmetry A.hom (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).inv) ≫ _ = _
  rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_snd,
    hq, ← Category.assoc, pullbackSymmetry_hom_comp_fst]

theorem over_endomorphism_descends_to_finite_coefficients
    (A : Over (Spec (CommRingCat.of R)))
    [QuasiCompact A.hom] [QuasiSeparated A.hom] [LocallyOfFinitePresentation A.hom]
    (k : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj A) :
    ∃ (s : (Finset B)ᵒᵖ)
      (a : (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).obj A ⟶
        (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).obj A),
      standardCoefficientProjection R B A s ≫ a.left =
        k.left ≫ standardCoefficientProjection R B A s := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let e := pullbackSymmetry A.hom p
  let k' : pullback A.hom p ⟶ pullback A.hom p := k.left
  have hkw : k' ≫ pullback.snd A.hom p = pullback.snd A.hom p := k.w
  let u := e.inv ≫ k' ≫ e.hom
  have hu : u ≫ pullback.fst p A.hom = pullback.fst p A.hom := by
    dsimp only [u, e]
    rw [Category.assoc, Category.assoc, pullbackSymmetry_hom_comp_fst,
      hkw, pullbackSymmetry_inv_comp_snd]
  obtain ⟨s, a, ha, heq⟩ := FiniteCoefficientFst.Abelian.scheme_endomorphism_descends_to_finite_coefficients R B A.hom u hu
  let d := pullbackSymmetry A.hom (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)
  have hw : (d.hom ≫ a ≫ d.inv) ≫ pullback.snd A.hom (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) =
      pullback.snd A.hom (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) := by
    dsimp only [d]
    rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_snd,
      ha, pullbackSymmetry_hom_comp_fst]
  let a' : (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).obj A ⟶
      (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).obj A :=
    Over.homMk (d.hom ≫ a ≫ d.inv) hw
  refine ⟨s, a', ?_⟩
  exact iso_conjugate_commuting_square e d ((FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B A.hom).π.app s) k' a heq

end

end OAI.ArithmeticGeometry.Descent.CMVariety.OverEndomorphism.Abelian
