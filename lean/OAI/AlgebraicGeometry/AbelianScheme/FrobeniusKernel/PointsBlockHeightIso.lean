import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors

/-! # Points Block Height Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockHeightIso.Construction

noncomputable section

section

/-! Equivariant source maps act on the exact CMPoints character-block
functors while preserving the original inclusions on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {O : Type} [CommRing O] {S : Scheme} {g q : ℕ} [Fact q.Prime]
variable (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B)
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]
variable (hf : ∀ a : O, ρ.map a ≫ f = f ≫ σ.map a)
variable (χ : O →+* PadicInt q) (n : ℕ)

def l45BlockPointsMap (T : Over S) :
    PELModuli.CMPoints.BlocksProjectors.blockPoints A ρ χ n T →* PELModuli.CMPoints.BlocksProjectors.blockPoints B σ χ n T where
  toFun x := ⟨x.val ≫ f, by
    refine ⟨?_, fun a => ?_⟩
    · rw [← MonObj.pow_comp, x.property.1, MonObj.one_comp]
    · exact (Category.assoc x.val f (σ.map a)).trans
        ((congrArg (fun z => x.val ≫ z) (hf a).symm).trans
          ((Category.assoc x.val (ρ.map a) f).symm.trans
            ((congrArg (fun z => z ≫ f) (x.property.2 a)).trans
              (MonObj.pow_comp x.val _ f))))⟩
  map_one' := Subtype.ext (MonObj.one_comp f)
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val f)

def l45BlockFunctorMap : PELModuli.CMPoints.BlocksProjectors.blockFunctor A ρ χ n ⟶ PELModuli.CMPoints.BlocksProjectors.blockFunctor B σ χ n where
  app T := GrpCat.ofHom (l45BlockPointsMap A B ρ σ f hf χ n T.unop)
  naturality {T U} a := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.assoc a.unop x.val f)

end

/-! An original equivariant source isomorphism transports the complete
CMPoints block-height witness, with the same q-divisible group and the exact
transition inclusions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {O : Type} [CommRing O] {S : Scheme} {g q : ℕ} [Fact q.Prime]
section Source

variable (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B)
variable (eA : A.scheme ≅ B.scheme) [IsMonHom eA.hom]
variable (he : ∀ a : O, ρ.map a ≫ eA.hom = eA.hom ≫ σ.map a)

include he in
omit [IsMonHom eA.hom] in
theorem l45ActionIso_inverse (a : O) : σ.map a ≫ eA.inv = eA.inv ≫ ρ.map a := by
  apply (cancel_epi eA.hom).mp
  rw [← Category.assoc, ← he a, Category.assoc, eA.hom_inv_id, Category.comp_id,
    eA.hom_inv_id_assoc]

variable (χ : O →+* PadicInt q) (n : ℕ)

def l45BlockFunctorIso : PELModuli.CMPoints.BlocksProjectors.blockFunctor A ρ χ n ≅ PELModuli.CMPoints.BlocksProjectors.blockFunctor B σ χ n where
  hom := l45BlockFunctorMap A B ρ σ eA.hom he χ n
  inv := l45BlockFunctorMap B A σ ρ eA.inv (l45ActionIso_inverse A B ρ σ eA he) χ n
  hom_inv_id := by
    apply NatTrans.ext
    funext T
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change (x.val ≫ eA.hom) ≫ eA.inv = x.val
    rw [Category.assoc, eA.hom_inv_id, Category.comp_id]
  inv_hom_id := by
    apply NatTrans.ext
    funext T
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change (x.val ≫ eA.inv) ≫ eA.hom = x.val
    rw [Category.assoc, eA.inv_hom_id, Category.comp_id]

end Source

variable {k : Type} [Field k]
variable (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B)
variable (eA : A.scheme ≅ B.scheme) [IsMonHom eA.hom]
variable (he : ∀ a : O, ρ.map a ≫ eA.hom = eA.hom ≫ σ.map a)

variable (χ : O →+* PadicInt q) (n : ℕ)

def l45AffineBlockFunctorIso :
    PELModuli.CMPoints.BlocksProjectors.affineBlockFunctor A ρ χ n ≅ PELModuli.CMPoints.BlocksProjectors.affineBlockFunctor B σ χ n :=
  Functor.isoWhiskerLeft (algSpec (.of k)).rightOp (l45BlockFunctorIso A B ρ σ eA he χ n)

include he in
theorem l45BlockHasHeight_iso {h : ℕ} (hA : PELModuli.CMPoints.BlocksProjectors.BlockHasHeight A ρ χ h) :
    PELModuli.CMPoints.BlocksProjectors.BlockHasHeight B σ χ h := by
  obtain ⟨G, e, ht⟩ := hA
  refine ⟨G, fun n => e n ≪≫ l45AffineBlockFunctorIso A B ρ σ eA he χ n, ?_⟩
  intro n R x
  change (((e (n + 1)).hom.app R) (x ≫ G.inclusion n)).val ≫ eA.hom =
    (((e n).hom.app R) x).val ≫ eA.hom
  exact congrArg (fun a => a ≫ eA.hom) (ht n R x)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockHeightIso.Construction
