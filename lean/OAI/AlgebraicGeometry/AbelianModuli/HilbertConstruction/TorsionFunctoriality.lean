import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme

/-! # Torsion Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Functoriality of the actual torsion group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g h k : ℕ} {S : Scheme.{u}}
variable {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S} {C : Abelian.Schemes.AbelianScheme k S}

/-- The geometric torsion inclusion is a monomorphism over the base. -/
instance Abelian.Schemes.AbelianScheme.torsionInclusion_mono (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) : Mono (A.torsionInclusion N) where
  right_cancellation _f _g w :=
    (A.torsionSchemePointsEquiv N _).injective (Subtype.ext w)

/-- A group-scheme morphism induces a morphism on torsion schemes. -/
def Abelian.Schemes.AbelianScheme.torsionMap (N : ℕ) (a : A.scheme ⟶ B.scheme) [IsMonHom a] :
    A.torsionScheme N ⟶ B.torsionScheme N :=
  (B.torsionSchemePointsEquiv N (A.torsionScheme N)).symm
    ⟨A.torsionInclusion N ≫ a, by
      change (A.torsionInclusion N ≫ a) ^ N = 1
      rw [← MonObj.pow_comp, A.torsionInclusion_pow, MonObj.one_comp]⟩

@[reassoc (attr := simp)]
theorem Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion (N : ℕ) (a : A.scheme ⟶ B.scheme) [IsMonHom a] :
    Abelian.Schemes.AbelianScheme.torsionMap N a ≫ B.torsionInclusion N = A.torsionInclusion N ≫ a :=
  congrArg (fun x : B.torsionPoints N (A.torsionScheme N) => x.val)
    ((B.torsionSchemePointsEquiv N (A.torsionScheme N)).apply_symm_apply _)

@[simp]
theorem Abelian.Schemes.AbelianScheme.torsionMap_id (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) :
    Abelian.Schemes.AbelianScheme.torsionMap N (𝟙 A.scheme) = 𝟙 (A.torsionScheme N) := by
  apply (cancel_mono (A.torsionInclusion N)).mp
  rw [Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion, Category.comp_id, Category.id_comp]

/-- The torsion construction preserves composition of group-scheme maps. -/
theorem Abelian.Schemes.AbelianScheme.torsionMap_comp (N : ℕ) (a : A.scheme ⟶ B.scheme) (b : B.scheme ⟶ C.scheme)
    [IsMonHom a] [IsMonHom b] :
    Abelian.Schemes.AbelianScheme.torsionMap N (a ≫ b) = Abelian.Schemes.AbelianScheme.torsionMap N a ≫ Abelian.Schemes.AbelianScheme.torsionMap N b := by
  apply (cancel_mono (C.torsionInclusion N)).mp
  simp only [Category.assoc, Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion, Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion_assoc]

/-- An isomorphism of abelian schemes induces an isomorphism of torsion schemes. -/
def Abelian.Schemes.AbelianScheme.torsionMapIso (N : ℕ) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    A.torsionScheme N ≅ B.torsionScheme N where
  hom := Abelian.Schemes.AbelianScheme.torsionMap N e.hom
  inv := Abelian.Schemes.AbelianScheme.torsionMap N e.inv
  hom_inv_id := by
    apply (cancel_mono (A.torsionInclusion N)).mp
    simp only [Category.assoc, Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion, Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion_assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (B.torsionInclusion N)).mp
    simp only [Category.assoc, Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion, Abelian.Schemes.AbelianScheme.torsionMap_comp_inclusion_assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
