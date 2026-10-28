import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Transport Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Composition, inversion, and cancellation for transport of the actual
full ordered level, expressed on every test-scheme basis. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {g N : ℕ} {S : Scheme.{u}} {A B C : Abelian.Schemes.AbelianScheme g S}
variable (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
variable (d : B.scheme ≅ C.scheme) [IsMonHom d.hom]

local instance Abelian.Schemes.AbelianScheme.FullLevel.transportComposite_isMonHom : IsMonHom (e ≪≫ d).hom :=
  inferInstanceAs (IsMonHom (e.hom ≫ d.hom))

local instance Abelian.Schemes.AbelianScheme.FullLevel.transportInverse_isMonHom : IsMonHom e.symm.hom :=
  inferInstanceAs (IsMonHom e.inv)

theorem Abelian.Schemes.AbelianScheme.FullLevel.transport_trans (l : A.FullLevel N) :
    (l.transport e).transport d = l.transport (e ≪≫ d) := by
  apply Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro T c
  change ((l.hom.app (.op T) c).val ≫ e.hom) ≫ d.hom =
    (l.hom.app (.op T) c).val ≫ (e.hom ≫ d.hom)
  exact Category.assoc _ _ _

theorem Abelian.Schemes.AbelianScheme.FullLevel.transport_symm (l : A.FullLevel N) : (l.transport e).transport e.symm = l := by
  apply Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro T c
  change ((l.hom.app (.op T) c).val ≫ e.hom) ≫ e.inv = (l.hom.app (.op T) c).val
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem Abelian.Schemes.AbelianScheme.FullLevel.transport_eq_iff (l : A.FullLevel N) (k : B.FullLevel N) :
    l.transport e = k ↔ l = k.transport e.symm := by
  constructor
  · intro h
    exact (Abelian.Schemes.AbelianScheme.FullLevel.transport_symm e l).symm.trans (congrArg (fun j => j.transport e.symm) h)
  · intro h
    rw [h]
    exact Abelian.Schemes.AbelianScheme.FullLevel.transport_symm e.symm k

theorem Abelian.Schemes.AbelianScheme.FullLevel.transport_injective : Function.Injective (fun l : A.FullLevel N => l.transport e) := by
  intro l k h
  exact (Abelian.Schemes.AbelianScheme.FullLevel.transport_symm e l).symm.trans
    ((congrArg (fun j => j.transport e.symm) h).trans (Abelian.Schemes.AbelianScheme.FullLevel.transport_symm e k))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
