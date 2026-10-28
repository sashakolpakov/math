import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.FamilyTransport
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupRigidity

/-! # Underlying Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnderlyingIso

noncomputable section

/-! Uniqueness of the represented homogeneous Picard sheaf gives an
actual dual scheme isomorphism. The origin condition and geometric
rigidity prove compatibility with the original group structures. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
    {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D E : HilbertConstruction.Dual.Data.DualAbelianData A)

omit [IsAlgClosed k] in
theorem dualUnderlyingIso_representation {T : Over (Spec (.of k))}
    (a : T ⟶ D.abelian.scheme) :
    E.representable.homEquiv (a ≫ (D.uniqueUnderlyingIso E).hom) =
      D.representable.homEquiv a := by
  change E.representable.homEquiv
    (a ≫ E.representable.homEquiv.symm (D.representable.homEquiv (𝟙 D.abelian.scheme))) = _
  rw [E.representable.comp_homEquiv_symm, Equiv.apply_symm_apply,
    ← D.representable.homEquiv_comp, Category.comp_id]

omit [IsAlgClosed k] in
theorem dualUnderlyingIso_origin {T : Over (Spec (.of k))} :
    (1 : T ⟶ D.abelian.scheme) ≫ (D.uniqueUnderlyingIso E).hom = 1 := by
  apply E.representable.homEquiv.injective
  exact (dualUnderlyingIso_representation D E 1).trans ((D.origin T).trans (E.origin T).symm)

instance dualUnderlyingIso_isMonHom : IsMonHom (D.uniqueUnderlyingIso E).hom := by
  apply Picard.Homomorphisms.GroupRigidity.Construction.pointed_isMonHom D.abelian.scheme E.abelian.scheme
  have h := dualUnderlyingIso_origin D E (T := 𝟙_ (Over (Spec (.of k))))
  simpa only [Hom.one_def, CategoryTheory.CartesianMonoidalCategory.toUnit_unit,
    Category.id_comp] using h

def dualFamilyIso {B : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (DB : HilbertConstruction.Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] : D.abelian.scheme ≅ DB.abelian.scheme :=
  (D.familyTransport e).uniqueUnderlyingIso DB

instance dualFamilyIso_isMonHom {B : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (DB : HilbertConstruction.Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] : IsMonHom (dualFamilyIso D DB e).hom :=
  dualUnderlyingIso_isMonHom (D.familyTransport e) DB

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnderlyingIso
