import OAI.ArithmeticGeometry.Descent.CMVariety.OverEndomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Abelian Coefficient Comparison -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AbelianCoefficientComparison

noncomputable section

/-! Group-preserving comparisons for the actual iterated coefficient fibers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

def iteratedAbelianPullbackIso
    {S S' S'' : Scheme} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') (p : S'' ⟶ S) (hp : h ≫ f = p) :
    ((A.pullback f).pullback h).scheme ≅ (A.pullback p).scheme :=
  (A.pullbackCompIso f h).symm ≪≫ A.pullbackCongrIso (h ≫ f) p hp

instance iteratedAbelianPullbackIso_group
    {S S' S'' : Scheme} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') (p : S'' ⟶ S) (hp : h ≫ f = p) :
    IsMonHom (iteratedAbelianPullbackIso A f h p hp).hom := by
  change IsMonHom ((A.pullbackCompIso f h).inv ≫ (A.pullbackCongrIso (h ≫ f) p hp).hom)
  infer_instance

theorem iteratedAbelianPullbackIso_inv_fst_fst
    {S S' S'' : Scheme} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (f : S' ⟶ S) (h : S'' ⟶ S') (p : S'' ⟶ S) (hp : h ≫ f = p) :
    (iteratedAbelianPullbackIso A f h p hp).inv.left ≫
      pullback.fst (A.pullback f).scheme.hom h ≫ pullback.fst A.scheme.hom f =
        pullback.fst A.scheme.hom p := by
  cases hp
  simp only [iteratedAbelianPullbackIso, Iso.trans_inv, Iso.symm_inv,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCongrIso, eqToIso_refl, Iso.refl_inv,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom]
  exact AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons.pullbackComp_hom_fst_fst A.scheme f h

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def coefficientInclusion (s : (Finset B)ᵒᵖ) :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R B s.unop) B))

theorem coefficientInclusion_base (s : (Finset B)ᵒᵖ) :
    coefficientInclusion R B s ≫ FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  FiniteCoefficientDiagram.Abelian.finiteCoefficientSchemeCone_structure R B s

def abelianCoefficientComparison {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R))) (s : (Finset B)ᵒᵖ) :
    ((A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).pullback (coefficientInclusion R B s)).scheme ≅
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).scheme :=
  iteratedAbelianPullbackIso A (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)
    (coefficientInclusion R B s) _ (coefficientInclusion_base R B s)

instance abelianCoefficientComparison_group {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R))) (s : (Finset B)ᵒᵖ) :
    IsMonHom (abelianCoefficientComparison R B A s).hom :=
  iteratedAbelianPullbackIso_group _ _ _ _ _

theorem abelianCoefficientComparison_inv_fst {g : ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (CommRingCat.of R))) (s : (Finset B)ᵒᵖ) :
    (abelianCoefficientComparison R B A s).inv.left ≫
      pullback.fst (A.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).scheme.hom
        (coefficientInclusion R B s) = OverEndomorphism.Abelian.standardCoefficientProjection R B A.scheme s := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let f := FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop
  let h := coefficientInclusion R B s
  let e := abelianCoefficientComparison R B A s
  let eInv : pullback A.scheme.hom p ⟶ pullback (pullback.snd A.scheme.hom f) h := e.inv.left
  let π : pullback (pullback.snd A.scheme.hom f) h ⟶ pullback A.scheme.hom f :=
    pullback.fst (pullback.snd A.scheme.hom f) h
  let q : pullback A.scheme.hom p ⟶ pullback A.scheme.hom f :=
    OverEndomorphism.Abelian.standardCoefficientProjection R B A.scheme s
  have hf : eInv ≫ π ≫ pullback.fst A.scheme.hom f = pullback.fst A.scheme.hom p :=
    iteratedAbelianPullbackIso_inv_fst_fst A f h p (coefficientInclusion_base R B s)
  have hw : eInv ≫ pullback.snd (pullback.snd A.scheme.hom f) h = pullback.snd A.scheme.hom p :=
    e.inv.w
  change eInv ≫ π = q
  apply pullback.hom_ext
  · rw [Category.assoc]
    exact hf.trans (OverEndomorphism.Abelian.standardCoefficientProjection_fst R B A.scheme s).symm
  · dsimp only [π]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    rw [hw]
    exact (OverEndomorphism.Abelian.standardCoefficientProjection_snd R B A.scheme s).symm

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AbelianCoefficientComparison
