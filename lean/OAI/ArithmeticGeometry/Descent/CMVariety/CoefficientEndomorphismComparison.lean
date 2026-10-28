import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianCoefficientComparison

/-! # Coefficient Endomorphism Comparison -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian

noncomputable section

section

/-!
The exact coefficient projection square determines the base-changed
endomorphism under the group-preserving fiber comparison.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def abelianPullbackEndomorphism
    {S S' : Scheme} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (q : S' ⟶ S)
    (a : A.scheme ⟶ A.scheme) : (A.pullback q).scheme ⟶ (A.pullback q).scheme :=
  (Over.pullback q).map a

theorem pullback_over_hom_ext
    {S S' : Scheme} (q : S' ⟶ S) (B : Over S) {T : Over S'}
    (a b : T ⟶ (Over.pullback q).obj B)
    (h : a.left ≫ pullback.fst B.hom q = b.left ≫ pullback.fst B.hom q) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact a.w.trans b.w.symm

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

theorem pullback_endomorphism_conjugation
    {S S' : Scheme} (q : S' ⟶ S) (X : Over S) (Y : Over S')
    (e : (Over.pullback q).obj X ≅ Y) (a : X ⟶ X) (k : Y ⟶ Y)
    (h : (e.inv.left ≫ pullback.fst X.hom q) ≫ a.left =
      k.left ≫ (e.inv.left ≫ pullback.fst X.hom q)) :
    (Over.pullback q).map a = e.hom ≫ k ≫ e.inv := by
  apply (cancel_epi e.inv).mp
  rw [e.inv_hom_id_assoc]
  apply pullback_over_hom_ext q X
  change (e.inv.left ≫ ((Over.pullback q).map a).left) ≫ pullback.fst X.hom q =
    (k.left ≫ e.inv.left) ≫ pullback.fst X.hom q
  rw [Category.assoc, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst, ← Category.assoc]
  exact h.trans (Category.assoc _ _ _).symm

theorem abelian_pullback_endomorphism_conjugation
    {S S' : Scheme} {g : ℕ} (q : S' ⟶ S)
    (X : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (Y : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S')
    (e : (X.pullback q).scheme ≅ Y.scheme)
    (a : X.scheme ⟶ X.scheme) (k : Y.scheme ⟶ Y.scheme)
    (h : (e.inv.left ≫ pullback.fst X.scheme.hom q) ≫ a.left =
      k.left ≫ (e.inv.left ≫ pullback.fst X.scheme.hom q)) :
    abelianPullbackEndomorphism X q a = e.hom ≫ k ≫ e.inv :=
  pullback_endomorphism_conjugation q X.scheme Y.scheme e a k h

theorem coefficient_endomorphism_baseChange_eq {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R))) (s : (Finset B)ᵒᵖ)
    (a : (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).scheme ⟶
      (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).scheme)
    (k : (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme ⟶
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme)
    (h : OverEndomorphism.Abelian.standardCoefficientProjection R B A.scheme s ≫ a.left =
      k.left ≫ OverEndomorphism.Abelian.standardCoefficientProjection R B A.scheme s) :
    abelianPullbackEndomorphism (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop))
      (AbelianCoefficientComparison.coefficientInclusion R B s) a =
      (AbelianCoefficientComparison.abelianCoefficientComparison R B A s).hom ≫ k ≫
        (AbelianCoefficientComparison.abelianCoefficientComparison R B A s).inv := by
  apply abelian_pullback_endomorphism_conjugation (AbelianCoefficientComparison.coefficientInclusion R B s)
    (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop))
    (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (AbelianCoefficientComparison.abelianCoefficientComparison R B A s) a k
  exact (congrArg (fun u => u ≫ a.left)
    (AbelianCoefficientComparison.abelianCoefficientComparison_inv_fst R B A s)).trans
      (h.trans (congrArg (fun u => k.left ≫ u)
        (AbelianCoefficientComparison.abelianCoefficientComparison_inv_fst R B A s).symm))

theorem coefficient_endomorphism_baseChange_group {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R))) (s : (Finset B)ᵒᵖ)
    (a : (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).scheme ⟶
      (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).scheme)
    (k : (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme ⟶
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme) [IsMonHom k]
    (h : OverEndomorphism.Abelian.standardCoefficientProjection R B A.scheme s ≫ a.left =
      k.left ≫ OverEndomorphism.Abelian.standardCoefficientProjection R B A.scheme s) :
    IsMonHom (abelianPullbackEndomorphism
      (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)) (AbelianCoefficientComparison.coefficientInclusion R B s) a) := by
  rw [coefficient_endomorphism_baseChange_eq R B A s a k h]
  infer_instance

end

/-! Naturality of the canonical group-preserving coefficient comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def ConjugateEndomorphisms
    {C : Type*} [Category* C] {X Y : C} (e : X ≅ Y)
    (a : X ⟶ X) (b : Y ⟶ Y) : Prop :=
  a = e.hom ≫ b ≫ e.inv

theorem iso_conjugation_of_naturality
    {C : Type*} [Category* C] {X Y : C} (e : X ≅ Y)
    (a : X ⟶ X) (b : Y ⟶ Y) (h : a ≫ e.hom = e.hom ≫ b) :
    ConjugateEndomorphisms e a b :=
  (e.eq_comp_inv.mpr h).trans (Category.assoc _ _ _)

theorem ConjugateEndomorphisms.trans
    {C : Type*} [Category* C] {X Y Z : C} (e : X ≅ Y) (d : Y ≅ Z)
    (a : X ⟶ X) (b : Y ⟶ Y) (c : Z ⟶ Z)
    (he : ConjugateEndomorphisms e a b) (hd : ConjugateEndomorphisms d b c) :
    ConjugateEndomorphisms (e ≪≫ d) a c := by
  dsimp only [ConjugateEndomorphisms] at he hd ⊢
  rw [he, hd]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]

theorem iteratedAbelianPullbackIso_naturality
    {S S' S'' : Scheme} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') (p : S'' ⟶ S) (hp : h ≫ f = p)
    (a : A.scheme ⟶ A.scheme) :
    abelianPullbackEndomorphism (A.pullback f) h (abelianPullbackEndomorphism A f a) ≫
        (AbelianCoefficientComparison.iteratedAbelianPullbackIso A f h p hp).hom =
      (AbelianCoefficientComparison.iteratedAbelianPullbackIso A f h p hp).hom ≫ abelianPullbackEndomorphism A p a := by
  cases hp
  simp only [AbelianCoefficientComparison.iteratedAbelianPullbackIso, Iso.trans_hom, Iso.symm_hom,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCongrIso, eqToIso_refl, Iso.refl_hom,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_inv]
  exact (Over.pullbackComp h f).inv.naturality a

theorem iteratedAbelianPullbackIso_conjugation
    {S S' S'' : Scheme} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') (p : S'' ⟶ S) (hp : h ≫ f = p)
    (a : A.scheme ⟶ A.scheme) :
    ConjugateEndomorphisms (AbelianCoefficientComparison.iteratedAbelianPullbackIso A f h p hp)
      (abelianPullbackEndomorphism (A.pullback f) h (abelianPullbackEndomorphism A f a))
      (abelianPullbackEndomorphism A p a) := by
  exact iso_conjugation_of_naturality (AbelianCoefficientComparison.iteratedAbelianPullbackIso A f h p hp)
    (abelianPullbackEndomorphism (A.pullback f) h (abelianPullbackEndomorphism A f a))
    (abelianPullbackEndomorphism A p a)
    (iteratedAbelianPullbackIso_naturality A f h p hp a)

theorem abelianCoefficientComparison_conjugation
    (R B : Type) [CommRing R] [CommRing B] [Algebra R B] {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R))) (s : (Finset B)ᵒᵖ)
    (a : A.scheme ⟶ A.scheme) :
    ConjugateEndomorphisms (AbelianCoefficientComparison.abelianCoefficientComparison R B A s)
      (abelianPullbackEndomorphism (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop))
        (AbelianCoefficientComparison.coefficientInclusion R B s)
          (abelianPullbackEndomorphism A (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop) a))
      (abelianPullbackEndomorphism A (Spec.map (CommRingCat.ofHom (algebraMap R B))) a) :=
  iteratedAbelianPullbackIso_conjugation A _ _ _ (AbelianCoefficientComparison.coefficientInclusion_base R B s) a

end

end OAI.ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian
