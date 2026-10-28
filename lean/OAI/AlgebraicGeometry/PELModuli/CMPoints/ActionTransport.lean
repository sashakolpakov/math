import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Action Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ActionTransport

noncomputable section

/-! Transport the full actual integral action along a group-scheme
isomorphism, retaining its intertwining equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

def integralActionOfIso {S : Scheme.{0}} {g h : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    {O : Type*} [CommRing O] (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B where
  map r := e.inv ≫ ρ.map r ≫ e.hom
  preservesGroup _ := inferInstance
  map_zero := by rw [ρ.map_zero, MonObj.one_comp, MonObj.comp_one]
  map_one := by rw [ρ.map_one, Category.id_comp, e.inv_hom_id]
  map_add r t := by rw [ρ.map_add, MonObj.mul_comp, MonObj.comp_mul]
  map_mul r t := by
    rw [ρ.map_mul]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem integralActionOfIso_intertwines {S : Scheme.{0}} {g h : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    {O : Type*} [CommRing O] (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (r : O) :
    ρ.map r ≫ e.hom = e.hom ≫ (integralActionOfIso e ρ).map r := by
  change ρ.map r ≫ e.hom = e.hom ≫ e.inv ≫ ρ.map r ≫ e.hom
  simp only [Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ActionTransport
