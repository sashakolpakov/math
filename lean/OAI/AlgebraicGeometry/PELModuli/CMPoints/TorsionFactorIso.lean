import OAI.AlgebraicGeometry.PELModuli.CMPoints.PrimeToDegreeTorsion
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FlattenTorsionFactors

/-! # Torsion Factor Iso -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.CMPoints.TorsionFactorIso

/-! Maps from abelian torsion to a finite product of factors, allowing
different factor dimensions and preserving all test-scheme functor maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g h : ℕ}

def torsionCommFunctor (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (N : ℕ) : (Over S)ᵒᵖ ⥤ CommGrpCat where
  obj T := CommGrpCat.of (A.torsionPoints N T.unop)
  map f := CommGrpCat.ofHom (A.torsionPullback N f.unop)
  map_id T := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.id_comp x.val)
  map_comp f k := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.assoc _ _ x.val)

def mixedHomOnTorsion (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] (N : ℕ) :
    A.torsionFunctor N ⟶ B.torsionFunctor N where
  app T := GrpCat.ofHom {
    toFun x := ⟨x.val ≫ f, by
      change (x.val ≫ f) ^ N = 1
      have hx : x.val ^ N = 1 := x.property
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]⟩
    map_one' := Subtype.ext (MonObj.one_comp _)
    map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val _) }
  naturality _ _ _ := by ext x; exact Subtype.ext (Category.assoc _ _ _)

variable {I : Type} [Fintype I] {d : I → ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (B : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) S)

def torsionFactorMap (f : ∀ i, A.scheme ⟶ (B i).scheme) (hf : ∀ i, IsMonHom (f i))
    (N : ℕ) : A.torsionFunctor N ⟶ FlattenTorsionFactors.piGroupFunctor (fun i => torsionCommFunctor (B i) N) where
  app T := GrpCat.ofHom (MonoidHom.pi (fun i =>
    letI := hf i; ((mixedHomOnTorsion A (B i) (f i) N).app T).hom))
  naturality T U a := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    funext i
    exact Subtype.ext (Category.assoc _ _ _)

def torsionFactorAssemble (f : ∀ i, (B i).scheme ⟶ A.scheme) (hf : ∀ i, IsMonHom (f i))
    (N : ℕ) : FlattenTorsionFactors.piGroupFunctor (fun i => torsionCommFunctor (B i) N) ⟶ A.torsionFunctor N :=
  FlattenTorsionFactors.piGroupCharacterAssemble (fun i => torsionCommFunctor (B i) N) (torsionCommFunctor A N)
    (fun i => letI := hf i; mixedHomOnTorsion (B i) A (f i) N)

theorem torsionFactorAssemble_val
    (f : ∀ i, (B i).scheme ⟶ A.scheme) (hf : ∀ i, IsMonHom (f i))
    (N : ℕ) (T : Over S) (x : ∀ i, (B i).torsionPoints N T) :
    ((torsionFactorAssemble A B f hf N).app (.op T) x).val = ∏ i, (x i).val ≫ f i := by
  let y (i : I) : A.torsionPoints N T :=
    letI := hf i
    (mixedHomOnTorsion (B i) A (f i) N).app (.op T) (x i)
  exact map_prod (A.torsionPoints N T).subtype y Finset.univ

structure AbelianScalarFactorization where
  multiplier : ℕ
  positive : 0 < multiplier
  forward : ∀ i, A.scheme ⟶ (B i).scheme
  backward : ∀ i, (B i).scheme ⟶ A.scheme
  forward_group : ∀ i, IsMonHom (forward i)
  backward_group : ∀ i, IsMonHom (backward i)
  diagonal : ∀ i, backward i ≫ forward i = (B i).multiplication multiplier
  offDiagonal : ∀ i j, i ≠ j → backward i ≫ forward j = 1
  total : (∏ i, forward i ≫ backward i) = A.multiplication multiplier

end AlgebraicGeometry.PELModuli.CMPoints.TorsionFactorIso

namespace AlgebraicGeometry.PELModuli.CMPoints.TorsionFactorIso.AbelianScalarFactorization

/-! An actual algebraic scalar splitting gives a torsion-functor
isomorphism at every order coprime to its multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {I : Type} [Fintype I] {g : ℕ} {d : I → ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (d i) S}
  (D : AbelianScalarFactorization A B)

theorem torsionFactorAssemble_factor (N : ℕ) (T : Over S) (x : A.torsionPoints N T) :
    (torsionFactorAssemble A B D.backward D.backward_group N).app (.op T)
      ((torsionFactorMap A B D.forward D.forward_group N).app (.op T) x) =
        x ^ D.multiplier := by
  apply Subtype.ext
  refine (torsionFactorAssemble_val A B D.backward D.backward_group N T
    ((torsionFactorMap A B D.forward D.forward_group N).app (.op T) x)).trans ?_
  change (∏ i, (x.val ≫ D.forward i) ≫ D.backward i) = x.val ^ D.multiplier
  have h := map_prod (A.pointsPullback x.val) (fun i => D.forward i ≫ D.backward i) Finset.univ
  change x.val ≫ (∏ i, D.forward i ≫ D.backward i) =
    ∏ i, x.val ≫ (D.forward i ≫ D.backward i) at h
  simp_rw [Category.assoc]
  rw [← h, D.total]
  simp only [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.multiplication, MonObj.comp_pow, Category.comp_id]

theorem torsionFactorMap_assemble (N : ℕ) (T : Over S)
    (x : ∀ i, (B i).torsionPoints N T) :
    (torsionFactorMap A B D.forward D.forward_group N).app (.op T)
      ((torsionFactorAssemble A B D.backward D.backward_group N).app (.op T) x) =
        x ^ D.multiplier := by
  classical
  funext i
  apply Subtype.ext
  change ((torsionFactorAssemble A B D.backward D.backward_group N).app (.op T) x).val ≫
    D.forward i = (x i).val ^ D.multiplier
  rw [torsionFactorAssemble_val]
  change (∏ j, (x j).val ≫ D.backward j) ≫ D.forward i = (x i).val ^ D.multiplier
  let : IsMonHom (D.forward i) := D.forward_group i
  have h := map_prod (IsMonHom.monoidHom (D.forward i) T)
    (fun j => (x j).val ≫ D.backward j) Finset.univ
  change (∏ j, (x j).val ≫ D.backward j) ≫ D.forward i =
    ∏ j, ((x j).val ≫ D.backward j) ≫ D.forward i at h
  rw [h, Finset.prod_eq_single i]
  · rw [Category.assoc, D.diagonal]
    simp only [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.multiplication, MonObj.comp_pow, Category.comp_id]
  · intro j _ hji
    rw [Category.assoc, D.offDiagonal j i hji, MonObj.comp_one]
  · simp

theorem torsionFactorMap_isIso (N : ℕ) (hN : N.Coprime D.multiplier) :
    IsIso (torsionFactorMap A B D.forward D.forward_group N) := by
  have (T : (Over S)ᵒᵖ) : IsIso ((torsionFactorMap A B D.forward D.forward_group N).app T) := by
    have hb := PrimeToDegreeTorsion.bijective_of_scalar_composites
      ((torsionFactorMap A B D.forward D.forward_group N).app T)
      ((torsionFactorAssemble A B D.backward D.backward_group N).app T)
      N D.multiplier hN
      (fun x => Subtype.ext x.property)
      (fun x => funext (fun i => Subtype.ext (x i).property))
      (D.torsionFactorAssemble_factor N T.unop) (D.torsionFactorMap_assemble N T.unop)
    exact (MulEquiv.toGrpIso (MulEquiv.ofBijective
      ((torsionFactorMap A B D.forward D.forward_group N).app T).hom hb)).isIso_hom
  exact NatIso.isIso_of_isIso_app _

def torsionFactorIso (N : ℕ) (hN : N.Coprime D.multiplier) :
    A.torsionFunctor N ≅ FlattenTorsionFactors.piGroupFunctor (fun i => torsionCommFunctor (B i) N) := by
  let := D.torsionFactorMap_isIso N hN
  exact asIso (torsionFactorMap A B D.forward D.forward_group N)

end AlgebraicGeometry.PELModuli.CMPoints.TorsionFactorIso.AbelianScalarFactorization

end

end OAI
